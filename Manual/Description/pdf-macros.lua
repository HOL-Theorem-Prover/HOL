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

-- Walk each Str element looking for replacement keys; emit a list
-- of Inlines (some Str, some replacement-returned).  Match only at
-- token boundaries: the key must be followed by a non-letter
-- (punctuation, end-of-string), so e.g. `HOL` matches in
-- "the HOL system" and "HOLs" stays untouched.
function Inlines(inlines)
  local function isLetter(c)
    return c:match("[A-Za-z]") ~= nil
  end
  local result = {}
  for _, elem in ipairs(inlines) do
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

function CodeBlock(item)
  if not FORMAT:match("latex") then
    return item
  end
  local _, count = string.gsub(item.text, "\n", "")
  -- Add 1 to account for the last line if it doesn't end with a newline
  -- or if the string contains only one line without a newline.
  -- If the string is empty, count will be 0.
  if #item.text > 0 and item.text:sub(#item.text) ~= "\n" then
      count = count + 1
  end
  -- Wrap in `alltt` (not `verbatim`): polyscripter output contains Unicode
  -- characters (turnstile, sum, infinity, the various lambda-calculus
  -- glyphs HOL prints) that desc-unicode.sty rewrites at LaTeX time;
  -- those declarations only fire inside command-processing environments,
  -- which `verbatim` is not but `alltt` is.  Long blocks still get
  -- wrapped in `samepage` to keep them on one page.
  local body = pandoc.RawBlock("latex",
    "\\begin{alltt}\n" .. escapeAlltt(item.text) .. "\n\\end{alltt}")
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
