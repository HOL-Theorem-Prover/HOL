-- Replacement table.  Each entry maps a literal source token to a
-- function returning a pandoc Inline.  `HOL` becomes a SmallCaps
-- inline (rendering equivalent to commands.tex's `\HOL = \textsc{Hol}`)
-- so that pandoc has a text-only fallback for PDF bookmarks --
-- using a RawInline `\HOL{}` would produce empty bookmark text and
-- emit `\texorpdfstring{... \HOL{} ...}{...  ...}` for headings.
-- The SML and REFERENCE macros have richer LaTeX styling
-- (small-font, small-italic) that smallcaps doesn't approximate
-- well, so they stay as raw LaTeX -- they're rare in headings.
local replacements = {
  HOL = function() return pandoc.SmallCaps({pandoc.Str("Hol")}) end,
  SML = function() return pandoc.RawInline("latex", "\\ML{}") end,
  REFERENCE = function()
    return pandoc.RawInline("latex", "\\REFERENCE{}")
  end
}

-- Match a RawInline against a literal HTML tag.  Pandoc always
-- emits these as exactly `<code>` / `</code>` (no whitespace, no
-- case variation), so a plain string compare suffices.
local function isHtmlTag(elem, tag)
  return elem.t == "RawInline" and elem.format == "html"
         and elem.text == tag
end

-- HTML `<br>` inside a pipe-table cell is dropped by pandoc's default
-- LaTeX writer, so the statement and proof in our euclid.smd theorem
-- tables collapse onto a single \texttt{} run.  Map it to `\newline`
-- (which works inside the p{width} columns pandoc uses for these
-- tables).  Returning Pandoc's `LineBreak` would risk being turned
-- into `\\` (a row separator) in a tabular cell.
function RawInline(elem)
  if elem.format == "html" and elem.text == "<br>" then
    return pandoc.RawInline("latex", "\\newline ")
  end
end

-- Leading non-breaking spaces at the start of a line in a p{} table
-- cell are silently stripped by LaTeX (verified empirically; happens
-- in longtable/tabular paragraph columns).  The `&nbsp;` indentation
-- we use in euclid.smd theorem-listing rows (between the arrow and
-- continuation lines) therefore vanishes in the PDF.  Replace any
-- leading nbsp run with \hspace*{} which is NOT stripped.  Width:
-- ~0.2em per nbsp matches the proportional-font visual offset of
-- the same nbsps in mdbook output.
function Str(elem)
  if not (FORMAT and FORMAT:match("latex")) then return nil end
  local text = elem.text
  local n = 0
  while text:sub(n*2 + 1, n*2 + 2) == "\xc2\xa0" do
    n = n + 1
  end
  if n == 0 then return nil end
  local hspace = pandoc.RawInline("latex",
                                  "\\hspace*{" .. (0.2 * n) .. "em}")
  local rest = text:sub(n*2 + 1)
  if #rest == 0 then return hspace end
  return { hspace, pandoc.Str(rest) }
end


-- Walk inlines, doing two things:
--   1. Collapse `<code>X</code>` HTML pairs into pandoc `Code` so
--      they render as \texttt{X} in the PDF (otherwise pandoc
--      passes through the bare HTML, which in LaTeX output just
--      drops the tags).  Note: assumes a text-only body -- any
--      `Emph`/`Math`/etc. inside is flattened to plain text via
--      stringify.  Fine for what we use it for (the
--      cross-pipeline `<code>&#124;&#124;</code>` trick for `||`
--      in pipe-table cells).
--   2. Replace bare tokens (`HOL`, `SML`, `REFERENCE`) inside
--      `Str` inlines with their PDF-friendly equivalents.  Match
--      only at token boundaries (next char must be non-letter)
--      so "HOL" matches in "the HOL system" but "HOLs" doesn't.
function Inlines(inlines)
  local function isLetter(c)
    return c:match("[A-Za-z]") ~= nil
  end
  -- Pass 1: fold `<code>...</code>` HTML pairs into Code inlines.
  local folded = {}
  local i = 1
  while i <= #inlines do
    local elem = inlines[i]
    if isHtmlTag(elem, "<code>") then
      local j, body, closed = i + 1, "", false
      while j <= #inlines do
        if isHtmlTag(inlines[j], "</code>") then
          closed = true
          break
        end
        body = body .. pandoc.utils.stringify(inlines[j])
        j = j + 1
      end
      if closed then
        table.insert(folded, pandoc.Code(body))
        i = j + 1
      else
        table.insert(folded, elem)
        i = i + 1
      end
    else
      table.insert(folded, elem)
      i = i + 1
    end
  end
  -- Pass 2: token-replace inside the remaining Str inlines.
  local result = {}
  for _, elem in ipairs(folded) do
    if elem.t == "Str" then
      local text = elem.text
      local i = 1
      local accum = ""
      local n = #text
      while i <= n do
        local matched = false
        for pat, fn in pairs(replacements) do
          local plen = #pat
          if i + plen - 1 <= n and text:sub(i, i + plen - 1) == pat then
            local nextc = i + plen <= n and text:sub(i + plen, i + plen) or ""
            if nextc == "" or not isLetter(nextc) then
              if #accum > 0 then
                table.insert(result, pandoc.Str(accum))
                accum = ""
              end
              table.insert(result, fn())
              i = i + plen
              matched = true
              break
            end
          end
        end
        if not matched then
          accum = accum .. text:sub(i, i)
          i = i + 1
        end
      end
      if #accum > 0 then
        table.insert(result, pandoc.Str(accum))
      end
    else
      table.insert(result, elem)
    end
  end
  return result
end

-- Escape `\`, `{`, `}` for inclusion inside an alltt environment.
-- Approach: use control char \1 as a temporary placeholder for `\` so
-- the brace escaping doesn't double-escape the braces inside
-- \textbackslash{}.
local function escapeAlltt(s)
  s = s:gsub("\\", "\1")
  s = s:gsub("{", "\\{")
  s = s:gsub("}", "\\}")
  s = s:gsub("\1", "\\textbackslash{}")
  return s
end

-- GFM alert blocks: `> [!NOTE]` / `[!TIP]` / `[!IMPORTANT]` /
-- `[!WARNING]` / `[!CAUTION]` followed by the body.  The marker
-- always sits on its own line, then optionally a blank quoted
-- line, then the body.  Pandoc parses the two forms as either
-- (a) one Para whose first inlines are `[!KIND]` then SoftBreak
-- then body, or (b) a Para containing only `[!KIND]` followed by
-- further blocks for the body.  Convert either to the matching
-- `\begin{holKIND}...\end{holKIND}` environment from
-- Manual/LaTeX/commands.tex (the LaTeX env emits the coloured
-- title row itself, so the marker is dropped here).
local alertEnv = {
  NOTE      = "holnote",
  TIP       = "holtip",
  IMPORTANT = "holimportant",
  WARNING   = "holwarning",
  CAUTION   = "holcaution",
}
function BlockQuote(item)
  if not FORMAT:match("latex") then return nil end
  local blocks = item.content
  if #blocks == 0 or blocks[1].t ~= "Para" then return nil end
  local inlines = blocks[1].content
  local breakAt = nil
  for i, e in ipairs(inlines) do
    if e.t == "SoftBreak" or e.t == "LineBreak" then
      breakAt = i; break
    end
  end
  local firstLine
  if breakAt then
    firstLine = {}
    for i = 1, breakAt - 1 do table.insert(firstLine, inlines[i]) end
  else
    firstLine = inlines
  end
  local kind = pandoc.utils.stringify(firstLine):match("^%[!(%u+)%]%s*$")
  if not kind or not alertEnv[kind] then return nil end
  local env = alertEnv[kind]
  local body = {}
  if breakAt then
    local rest = {}
    for i = breakAt + 1, #inlines do table.insert(rest, inlines[i]) end
    if #rest > 0 then table.insert(body, pandoc.Para(rest)) end
  end
  for i = 2, #blocks do table.insert(body, blocks[i]) end
  local out = {pandoc.RawBlock("latex", "\\begin{" .. env .. "}")}
  for _, b in ipairs(body) do table.insert(out, b) end
  table.insert(out, pandoc.RawBlock("latex", "\\end{" .. env .. "}"))
  return out
end

function CodeBlock(item)
  if not FORMAT:match("latex") then
    return item
  end
  -- Wrap in `alltt` (not `verbatim`): polyscripter output contains Unicode
  -- characters (turnstile, sum, infinity, the various lambda-calculus
  -- glyphs HOL prints) that desc-unicode.sty rewrites at LaTeX time;
  -- those declarations only fire inside command-processing environments,
  -- which `verbatim` is not but `alltt` is.
  local alltt =
    "\\begin{alltt}\n" .. escapeAlltt(item.text) .. "\n\\end{alltt}"
  -- ```repl blocks (polyscripter REPL interactions) get wrapped in the
  -- `session` environment from LaTeX/commands.tex, which draws the
  -- numbered left-bar/right-tab box that the original .stex manuals
  -- used.  session's minipage already keeps the block together on one
  -- page, so the samepage wrap is unnecessary for these.
  if item.classes:includes("repl") then
    return pandoc.RawBlock("latex",
      "\\begin{session}" .. alltt .. "\\end{session}")
  end
  -- Plain code blocks: count lines so we can decide whether to wrap
  -- long ones in samepage (keeps them on one page).
  local _, count = string.gsub(item.text, "\n", "")
  if #item.text > 0 and item.text:sub(#item.text) ~= "\n" then
      count = count + 1
  end
  -- Plain code blocks: just the alltt; longer ones get samepage so
  -- they don't break across pages.
  local body = pandoc.RawBlock("latex", alltt)
  if count > 3 then
    return {
      pandoc.RawBlock("latex", "\\begin{samepage}"),
      body,
      pandoc.RawBlock("latex", "\\end{samepage}")
    }
  else
    return body
  end
end
