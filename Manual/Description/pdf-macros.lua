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

function CodeBlock(item)
  local _, count = string.gsub(item.text, "\n", "")
  -- Add 1 to account for the last line if it doesn't end with a newline
  -- or if the string contains only one line without a newline.
  -- If the string is empty, count will be 0.
  if #item.text > 0 and item.text:sub(#item.text) ~= "\n" then
      count = count + 1
  end
  if count > 3 and FORMAT:match("latex") then
    return {
      pandoc.RawBlock("latex", "\\begin{samepage}"),
      item,
      pandoc.RawBlock("latex", "\\end{samepage}")
    }
  else
   return item
  end
end
