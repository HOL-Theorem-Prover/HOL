-- An eval's reports as lines to show, with highlights. An uncaught HOL_ERR
-- comes back as Poly/ML prints the exception value, strings escaped and all;
-- that's read back here and laid out the way HOL itself would report it.
local M = {}

---@class hol4.Line
---@field text string
---@field hl? [integer, integer, string][] byte ranges, end exclusive

local function set_hl()
  local function link(name, to)
    vim.api.nvim_set_hl(0, name, { link = to, default = true })
  end
  link('Hol4EvalText', 'NormalFloat')
  link('Hol4EvalError', 'DiagnosticError')
  link('Hol4EvalWarning', 'DiagnosticWarn')
  link('Hol4EvalLabel', '@label')
  link('Hol4EvalType', '@type')
  link('Hol4EvalOrigin', '@function')
  link('Hol4EvalDetail', 'Comment')
end
set_hl()
vim.api.nvim_create_autocmd('ColorScheme', {
  group = vim.api.nvim_create_augroup('hol4report', { clear = true }),
  callback = set_hl,
})

-- Reading Poly/ML's printout of a value ------------------------------------

local escapes = {
  a = '\a',
  b = '\b',
  t = '\t',
  n = '\n',
  v = '\v',
  f = '\f',
  r = '\r',
  ['"'] = '"',
  ['\\'] = '\\',
}

-- The SML string literal starting at `s[i]` (the opening quote): its value,
-- and the index after the closing quote
---@return string?, integer
local function read_string(s, i)
  local out = {}
  i = i + 1
  while i <= #s do
    local c = s:sub(i, i)
    if c == '"' then return table.concat(out), i + 1 end
    if c ~= '\\' then
      table.insert(out, c)
      i = i + 1
    else
      local e = s:sub(i + 1, i + 1)
      if escapes[e] then
        table.insert(out, escapes[e])
        i = i + 2
      elseif e:match('%d') then
        table.insert(out, string.char(tonumber(s:sub(i + 1, i + 3)) % 256))
        i = i + 4
      elseif e == '^' then
        table.insert(out, string.char(s:byte(i + 2) - 64))
        i = i + 3
      elseif e == 'u' then
        table.insert(out, vim.fn.nr2char(tonumber(s:sub(i + 2, i + 5), 16)))
        i = i + 6
      else
        -- A gap, `\<whitespace>\`, which a long string is broken over
        local stop = s:find('\\', i + 1, true)
        if not stop then return nil, i end
        i = stop + 1
      end
    end
  end
  return nil, i
end

---@alias hol4.Value
---| { str: string }
---| { con: string, arg?: hol4.Value }
---| { list: hol4.Value[] }
---| { tuple: hol4.Value[] }
---| { record: table<string, hol4.Value> }

-- Parse a value: strings, numbers, constructors, lists, tuples and records,
-- which is all an exception's contents come to here
---@param s string
---@return hol4.Value?
local function parse(s)
  local i = 1
  local function skip() i = s:find('[^%s]', i) or #s + 1 end
  local value

  local function seq(close, item)
    local items = {}
    skip()
    if s:sub(i, i) == close then
      i = i + 1
      return items
    end
    while true do
      table.insert(items, item())
      skip()
      local c = s:sub(i, i)
      i = i + 1
      if c == close then return items end
      if c ~= ',' then error('expected , or ' .. close) end
    end
  end

  local function atom()
    skip()
    local c = s:sub(i, i)
    if c == '"' then
      local str, j = read_string(s, i)
      if not str then error('unterminated string') end
      i = j
      return { str = str }
    elseif c == '[' then
      i = i + 1
      return { list = seq(']', value) }
    elseif c == '(' then
      i = i + 1
      local items = seq(')', value)
      return #items == 1 and items[1] or { tuple = items }
    elseif c == '{' then
      i = i + 1
      local record = {}
      seq('}', function()
        skip()
        local name, j = s:match("^([%w_']+)%s*=()", i)
        if not name then error('expected a field') end
        i = j
        record[name] = value()
        return true
      end)
      return { record = record }
    end
    local word, j = s:match("^(~?[%w_'.$]+)()", i)
    if not word then error('unexpected ' .. c) end
    i = j
    return { con = word }
  end

  -- An atom, applied to the next if it's a constructor that takes one
  function value()
    local v = atom()
    skip()
    if v.con and v.con:match('^%u') and s:sub(i, i):match('[%("{%[%w]') then
      v.arg = atom()
    end
    return v
  end

  local ok, v = pcall(value)
  return ok and v or nil
end

-- The first `{line, col}` (0-based) a HOL `locn` mentions, if any
---@param v hol4.Value?
---@return integer[]?
local function locn_start(v)
  if not v then return end
  if v.con == 'LocA' and v.arg and v.arg.tuple then
    local line, col = v.arg.tuple[1].con, v.arg.tuple[2].con
    return { tonumber(line), tonumber(col) }
  end
  for _, sub in ipairs(v.arg and (v.arg.tuple or { v.arg }) or {}) do
    local found = locn_start(sub)
    if found then return found end
  end
end

-- HOL_ERR -------------------------------------------------------------------

---@param lines hol4.Line[]
---@param text string
---@param group? string for the first line (default: `Hol4EvalError`)
local function add_message(lines, text, group)
  local first = true
  for _, line in ipairs(vim.split(text, '\n', { plain = true })) do
    local hl = {}
    -- `  Function: term :type`, as HOL's type errors put it
    local label_end = line:match('^%s*[%a][%w ]-:()%s')
    if first then
      table.insert(hl, { 0, #line, group or 'Hol4EvalError' })
    elseif label_end then
      local indent = #line:match('^%s*')
      table.insert(hl, { indent, label_end - 1, 'Hol4EvalLabel' })
      local colon = line:find(' :[^ ]', label_end)
      while colon do
        local next = line:find(' :[^ ]', colon + 1)
        if not next then break end
        colon = next
      end
      if colon then table.insert(hl, { colon, #line, 'Hol4EvalType' }) end
    end
    table.insert(lines, { text = line, hl = hl })
    first = false
  end
end

-- Lay out an uncaught HOL_ERR, from where Poly printed it, or return false if
-- `msg` isn't one. `at` is where the code ran ({row, col}: 1-based row, byte
-- col), which the error's locations are relative to.
---@param lines hol4.Line[]
---@param msg string
---@param at integer[]
---@return boolean
local function add_hol_err(lines, msg, at)
  local body = msg:match('^Exception%-?%s+HOL_ERR%s*(.-)%s*raised%s*$')
  local v = body and parse(body)
  local fields = v and v.con == 'HOL_ERROR' and v.arg and v.arg.record
  if not (fields and fields.message and fields.message.str) then
    return false
  end

  add_message(lines, vim.trim(fields.message.str))

  -- Origins run outermost first: the last is what raised it
  local origins = {}
  for _, o in ipairs(fields.origins and fields.origins.list or {}) do
    local r = o.record or {}
    local name = ('%s.%s'):format(
      r.origin_structure and r.origin_structure.str or '?',
      r.origin_function and r.origin_function.str or '?'
    )
    table.insert(origins, { name = name, at = locn_start(r.source_location) })
  end
  local raiser = table.remove(origins)
  if not raiser then return true end

  table.insert(lines, { text = '' })
  local line, hl = '', {}
  local function put(text, group)
    if group then table.insert(hl, { #line, #line + #text, group }) end
    line = line .. text
  end
  put(raiser.name, 'Hol4EvalOrigin')
  if raiser.at then
    local row, col = at[1] + raiser.at[1], raiser.at[2] + 1
    if raiser.at[1] == 0 then col = col + at[2] end
    put((' at line %d, column %d'):format(row, col), 'Hol4EvalDetail')
  end
  if #origins > 0 then
    put(', via ', 'Hol4EvalDetail')
    for k = #origins, 1, -1 do
      put(origins[k].name, 'Hol4EvalOrigin')
      if k > 1 then put(', ', 'Hol4EvalDetail') end
    end
  end
  table.insert(lines, { text = line, hl = hl })
  return true
end

---@param reports table[]
---@param at integer[] where the code ran ({row, col}: 1-based row, byte col)
---@return hol4.Line[]
function M.format(reports, at)
  local lines = {}
  -- Bodies are text, not lines: Poly prints a value an item at a time
  local out = ''
  local function flush()
    if out == '' then return end
    for _, text in
      ipairs(vim.split(out:gsub('\n$', ''), '\n', { plain = true }))
    do
      table.insert(lines, { text = text })
    end
    out = ''
  end
  for _, r in ipairs(reports) do
    if r.kind == 'toplevelOut' or r.kind == 'compilerOut' then
      out = out .. r.body
    elseif r.kind == 'error' then
      flush()
      if #lines > 0 then table.insert(lines, { text = '' }) end
      if not add_hol_err(lines, r.msg, at) then
        -- Any other exception: at least spell out the characters its strings
        -- print as escapes
        local text = r.msg:gsub('\n$', '')
        if text:match('^Exception') then
          text = text:gsub(
            '\\(%d%d%d)',
            function(d) return string.char(tonumber(d) % 256) end
          )
        end
        add_message(
          lines,
          text,
          r.hard and 'Hol4EvalError' or 'Hol4EvalWarning'
        )
        local start = r.pos.start
        local col = (start.character or 0) + 1
        if start.line == 0 then col = col + at[2] end
        local where = ('%s at line %d, column %d'):format(
          r.hard and 'error' or 'warning',
          at[1] + start.line,
          col
        )
        table.insert(lines, { text = '' })
        table.insert(
          lines,
          { text = where, hl = { { 0, #where, 'Hol4EvalDetail' } } }
        )
      end
    elseif r.kind == 'interrupted' then
      flush()
      table.insert(
        lines,
        { text = '[interrupted]', hl = { { 0, 13, 'Hol4EvalDetail' } } }
      )
    end
  end
  flush()
  return lines
end

M._parse = parse

return M
