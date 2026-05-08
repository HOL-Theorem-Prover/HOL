-- Define a table of replacements: keys are patterns, values are LaTeX macros
local replacements = {
  ["HOL"] = "\\HOL{}",
  ["SML"] = "\\ML{}",
  ["REFERENCE"] = "\\REFERENCE{}"
}

function Inlines(inlines)
  local result = {}
  for _, elem in ipairs(inlines) do
    if elem.t == "Str" then
      local text = elem.text
      local replaced = false
      for pattern, macro in pairs(replacements) do
        -- Match the pattern followed optionally by punctuation
        text = text:gsub(pattern .. "([%p]?)", function(punct)
          replaced = true
          return macro .. punct
        end)
      end
      if replaced then
        table.insert(result, pandoc.RawInline("latex", text))
      else
        table.insert(result, elem)
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
