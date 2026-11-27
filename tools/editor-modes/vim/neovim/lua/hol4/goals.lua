-- Goals pane for `bin/hol lsp`: the goal state at the cursor, from
-- `$/hol/goalState`.
local M = {}

M.follow = true

local ns = vim.api.nvim_create_namespace('hol4goals')
local state = {
  buf = nil, ---@type integer?
  win = nil, ---@type integer?
  -- Where the shown state was asked for; `mark` is an extmark at that
  -- position, which edits move along with the text
  src = nil, ---@type { buf: integer, win: integer, mark?: integer }?
  req = nil, ---@type { client: vim.lsp.Client, id: integer }?
  last = nil, ---@type string?
  ---@type { row: integer, scol: integer, ecol: integer, doc: string }[]
  docs = {},
  -- What each step took, by buffer, theorem and step. The server reports only
  -- the steps a request actually ran, so a cached step's time is kept here.
  costs = {}, ---@type table<integer, table<string, table<integer, integer>>>
}
local timer = assert(vim.uv.new_timer())

local kind_hl = {
  bv = 'Hol4GoalsBound',
  fv = 'Hol4GoalsFree',
  const = 'Hol4GoalsConst',
  tyv = 'Hol4GoalsTyvar',
}
local function set_hl()
  vim.api.nvim_set_hl(
    0,
    'Hol4GoalsBound',
    { link = '@variable.parameter', default = true }
  )
  vim.api.nvim_set_hl(
    0,
    'Hol4GoalsFree',
    { link = '@variable.builtin', default = true }
  )
  vim.api.nvim_set_hl(
    0,
    'Hol4GoalsConst',
    { link = '@function', default = true }
  )
  vim.api.nvim_set_hl(0, 'Hol4GoalsTyvar', { link = '@type', default = true })
  vim.api.nvim_set_hl(0, 'Hol4GoalsTitle', { link = 'WinBar', default = true })
  vim.api.nvim_set_hl(
    0,
    'Hol4GoalsApplying',
    { link = 'Comment', default = true }
  )
end
set_hl()

-- What to say about a symbol: a constant by theory and type, a variable by type
-- (as hol-mode.el)
local function segment_doc(seg)
  if not seg.kind then return nil end
  if seg.name and seg.ty then return seg.name .. ' : ' .. seg.ty end
  if seg.name then return seg.name end
  if seg.ty and seg.kind == 'bv' then return 'bound ' .. seg.ty end
  return seg.ty
end

local function show_doc()
  local row, col = unpack(vim.api.nvim_win_get_cursor(0))
  for _, d in ipairs(state.docs) do
    if d.row == row - 1 and col >= d.scol and col < d.ecol then
      vim.lsp.util.open_floating_preview({ d.doc }, 'text', { focus = false })
      return
    end
  end
end

local function get_buf()
  if state.buf and vim.api.nvim_buf_is_valid(state.buf) then
    return state.buf
  end
  local buf = vim.api.nvim_create_buf(false, true)
  vim.api.nvim_buf_set_name(buf, 'hol4://goals')
  vim.bo[buf].filetype = 'hol4goals'
  vim.bo[buf].bufhidden = 'hide'
  vim.bo[buf].modifiable = false
  local hol = require('hol4')
  local keys = hol.opts.goals.keys or {}
  hol._map(buf, keys.close, function() M.close() end, 'Close goals')
  hol._map(buf, keys.info, show_doc, 'Symbol type')
  state.buf = buf
  return buf
end

function M.is_open()
  return state.win ~= nil and vim.api.nvim_win_is_valid(state.win)
end

---@return integer?
function M.win() return M.is_open() and state.win or nil end

local function width()
  -- The server breaks lines at this width; leave room for the gutter.
  return M.is_open() and math.max(vim.api.nvim_win_get_width(state.win) - 2, 40)
    or 75
end

-- Remember what each step the server ran took
---@param buf integer
---@param result table a `$/hol/goalState` reply
local function record_costs(buf, result)
  local costs = result.stepCosts
  -- A walk cut short has a step in flight that no cost entry stands for, so
  -- entries can't be counted back from `step`
  local failed = result.error ~= nil and result.error ~= vim.NIL
  if type(costs) ~= 'table' or failed or result.status == 'pending' then
    return
  end
  state.costs[buf] = state.costs[buf] or {}
  local times = state.costs[buf][result.theorem] or {}
  state.costs[buf][result.theorem] = times
  for i, cost in ipairs(costs) do
    times[result.step - #costs + i] = cost.ms
  end
end

-- How long the step that produced `result` took, for display, if known
---@param result table
---@return string?
local function step_time(result)
  local src = state.src
  local times = src
    and state.costs[src.buf]
    and state.costs[src.buf][result.theorem]
  local ms = times and times[result.step]
  if not ms then return nil end
  return ms >= 1000 and ('%.2fs'):format(ms / 1000) or ms .. 'ms'
end

---@param result table?
---@return string winbar, string[] lines, table marks
local function layout(result)
  if result == nil then return ' not in a proof', {}, {} end

  local nil_ = function(v) return v ~= vim.NIL and v or nil end
  local err, note = nil_(result.error), nil_(result.note)
  local pending = result.status == 'pending'
  local goals = nil_(result.goals)

  local bar = { (' %s · step %d'):format(result.theorem, result.step) }
  local time = step_time(result)
  if time then bar[1] = bar[1] .. ' · ' .. time end
  if result.context and #result.context > 0 then
    table.insert(bar, '[' .. table.concat(result.context, '] [') .. ']')
  end
  if note then
    table.insert(bar, (note:gsub(':$', '')))
  elseif goals and #goals == 0 and not err and not pending then
    table.insert(bar, '✓ solved')
  end
  if pending then table.insert(bar, '(compiling…)') end

  -- Body from `segments`, which concatenate to `pretty` minus its colour
  -- escapes and say what each symbol is; `pretty` stripped of escapes when
  -- they're absent.
  local lines, marks = { '' }, {}
  local segments = nil_(result.segments)
  if not segments then
    local pretty = (nil_(result.pretty) or ''):gsub('\27%[[%d;]*m', '')
    segments = { { text = pretty } }
  end
  for _, seg in ipairs(segments) do
    local pieces = vim.split(seg.text or '', '\n', { plain = true })
    for i, piece in ipairs(pieces) do
      if i > 1 then table.insert(lines, '') end
      local row, scol = #lines, #lines[#lines]
      lines[row] = lines[row] .. piece
      if #pieces == 1 and seg.kind and #piece > 0 then
        table.insert(marks, {
          row = row - 1,
          scol = scol,
          ecol = scol + #piece,
          kind = seg.kind,
          doc = segment_doc(seg),
        })
      end
    end
  end
  -- `pretty` opens with a blank line; drop leading/trailing blanks
  local drop = 0
  while #lines > 0 and lines[1]:match('^%s*$') do
    table.remove(lines, 1)
    drop = drop + 1
  end
  while #lines > 0 and lines[#lines]:match('^%s*$') do
    table.remove(lines)
  end
  for _, m in ipairs(marks) do
    m.row = m.row - drop
  end

  if err then
    if #lines > 0 then table.insert(lines, '') end
    table.insert(marks, { row = #lines, line_hl = 'DiagnosticError' })
    for _, l in ipairs(vim.split(err, '\n', { plain = true })) do
      table.insert(lines, l)
    end
  end
  return table.concat(bar, '  '), lines, marks
end

---@param result table?
local function render(result)
  -- Refused outright (still loading or compiling): keep what's shown, wait for
  -- $/compileCompleted
  if result and result.status == 'pending' and result.theorem == nil then
    if M.is_open() and state.last then
      vim.wo[state.win].winbar = (
        vim.wo[state.win].winbar:gsub('  %(compiling…%)$', '')
      ) .. '  (compiling…)'
    end
    return
  end

  local bar, lines, marks = layout(result)
  local key = bar .. '\0' .. table.concat(lines, '\n')
  if key == state.last or not M.is_open() then return end
  state.last = key

  local buf = get_buf()
  vim.bo[buf].modifiable = true
  vim.api.nvim_buf_set_lines(buf, 0, -1, false, lines)
  vim.bo[buf].modifiable = false
  vim.api.nvim_buf_clear_namespace(buf, ns, 0, -1)
  state.docs = {}
  for _, m in ipairs(marks) do
    if m.line_hl then
      for row = m.row, #lines - 1 do
        vim.api.nvim_buf_set_extmark(
          buf,
          ns,
          row,
          0,
          { line_hl_group = m.line_hl }
        )
      end
    else
      if kind_hl[m.kind] then
        vim.api.nvim_buf_set_extmark(
          buf,
          ns,
          m.row,
          m.scol,
          { end_col = m.ecol, hl_group = kind_hl[m.kind] }
        )
      end
      if m.doc then table.insert(state.docs, m) end
    end
  end

  vim.wo[state.win].winbar = bar:gsub('%%', '%%%%')
  -- The current goal is listed last, so show the end
  vim.api.nvim_win_call(state.win, function()
    vim.api.nvim_win_set_cursor(0, { math.max(#lines, 1), 0 })
    vim.cmd('normal! zb')
  end)
end

-- A slow walk: keep showing the last state, and say a tactic is running
local function show_applying()
  if not M.is_open() then return end
  local buf = get_buf()
  local count = vim.api.nvim_buf_line_count(buf)
  local note = 'Applying tactic…'
  vim.bo[buf].modifiable = true
  vim.api.nvim_buf_set_lines(buf, count, count, false, { '', note })
  vim.bo[buf].modifiable = false
  vim.api.nvim_buf_set_extmark(buf, ns, count + 1, 0, {
    end_col = #note,
    hl_group = 'Hol4GoalsApplying',
  })
  -- Whatever comes back replaces this, even if it's the same state
  state.last = nil
  vim.api.nvim_win_call(state.win, function()
    vim.api.nvim_win_set_cursor(0, { count + 2, 0 })
    vim.cmd('normal! zb')
  end)
end

local src_ns = vim.api.nvim_create_namespace('hol4goals_src')

-- Ask for the goal state at the cursor of `win`, or at `pos` ({row, col}:
-- 1-based row, byte col), and show it
---@param buf integer
---@param win integer
---@param pos? integer[]
local function request(buf, win, pos)
  if
    vim.bo[buf].filetype ~= 'hol4script'
    or vim.api.nvim_win_get_buf(win) ~= buf
  then
    return
  end
  local client = vim.lsp.get_clients({ bufnr = buf, name = 'hol' })[1]
  if not client then return end

  if state.req then state.req.client:cancel_request(state.req.id) end
  local old = state.src
  -- A cursor in a line's indentation sits between the same tactics as one on
  -- its first non-blank character, but the server answers there with a
  -- half-run state (`∀m. …` after `rpt strip_tac`); so ask about the first
  -- non-blank instead.
  pos = pos or vim.api.nvim_win_get_cursor(win)
  local indent = #(
    vim.api.nvim_buf_get_lines(buf, pos[1] - 1, pos[1], false)[1] or ''
  ):match('^%s*')
  pos = { pos[1], math.max(pos[2], indent) }
  if old and old.mark and vim.api.nvim_buf_is_valid(old.buf) then
    vim.api.nvim_buf_del_extmark(old.buf, src_ns, old.mark)
  end
  state.src = {
    buf = buf,
    win = win,
    mark = vim.api.nvim_buf_set_extmark(buf, src_ns, pos[1] - 1, pos[2], {}),
  }
  local params =
    vim.lsp.util.make_given_range_params(pos, pos, buf, client.offset_encoding)
  params = { textDocument = params.textDocument, position = params.range.start }
  params.width = width()
  local ok, id
  ok, id = client:request('$/hol/goalState', params, function(err, result)
    -- A superseded request: cancelled (which this server answers as an
    -- "Interrupt" error) or simply slower than the one that replaced it
    if not (state.req and state.req.id == id) then return end
    state.req = nil
    if err then
      vim.notify('hol4: goal state: ' .. err.message, vim.log.levels.WARN)
      return
    end
    if result == vim.NIL then result = nil end
    if result then record_costs(buf, result) end
    require('hol4.proofs').on_goal_state(buf, pos[1], result)
    render(result)
  end, buf)
  if ok and id then
    local req = { client = client, id = id }
    state.req = req
    -- Most walks come back from the server's cache at once; say what a slow
    -- one is doing, so the pane doesn't look stuck
    vim.defer_fn(function()
      if state.req == req then show_applying() end
    end, 250)
  end
end

-- Ask again for the state on show, at the position it was asked for
local function reshow()
  local src = state.src
  if
    not (
      src
      and src.mark
      and vim.api.nvim_buf_is_valid(src.buf)
      and vim.api.nvim_win_is_valid(src.win)
    )
  then
    return
  end
  local at = vim.api.nvim_buf_get_extmark_by_id(src.buf, src_ns, src.mark, {})
  if at[1] then request(src.buf, src.win, { at[1] + 1, at[2] }) end
end

---@param buf? integer
---@param win? integer
function M.refresh(buf, win)
  request(
    buf or vim.api.nvim_get_current_buf(),
    win or vim.api.nvim_get_current_win()
  )
end

-- Debounced refresh, for cursor movement and edits
function M.schedule()
  if not (M.follow and M.is_open()) then return end
  local buf, win =
    vim.api.nvim_get_current_buf(), vim.api.nvim_get_current_win()
  timer:stop()
  timer:start(
    150,
    0,
    vim.schedule_wrap(function()
      if vim.api.nvim_buf_is_valid(buf) and vim.api.nvim_win_is_valid(win) then
        M.refresh(buf, win)
      end
    end)
  )
end

-- Called on $/compileCompleted: a pending answer for `uri` can now be given
---@param uri string
function M.on_compiled(uri)
  local src = state.src
  if
    not (
      M.is_open()
      and src
      and vim.api.nvim_buf_is_valid(src.buf)
      and vim.api.nvim_win_is_valid(src.win)
    )
  then
    return
  end
  if vim.uri_from_bufnr(src.buf) ~= uri then return end
  if M.follow then
    M.refresh(src.buf, src.win)
  else
    -- The same proof step as before, wherever the cursor is
    reshow()
  end
end

function M.open()
  if M.is_open() then return end
  local opts = require('hol4').opts.goals or {}
  local src_win = vim.api.nvim_get_current_win()
  local w = vim.api.nvim_win_get_width(src_win)
  local side = opts.position == 'right' or opts.position ~= 'below' and w >= 160
  state.win = vim.api.nvim_open_win(get_buf(), false, {
    split = side and 'right' or 'below',
    win = src_win,
    width = side and (opts.width or math.floor(w / 3)) or nil,
    height = (not side) and (opts.height or 15) or nil,
  })
  for opt, val in pairs {
    number = false,
    relativenumber = false,
    signcolumn = 'no',
    foldcolumn = '0',
    statuscolumn = '',
    list = false,
    spell = false,
    wrap = true,
    linebreak = true,
    -- The pane is rarely focused, and its title is worth reading all the same
    winhighlight = 'WinBarNC:Hol4GoalsTitle,WinBar:Hol4GoalsTitle',
    winfixbuf = true,
    winfixwidth = side,
    winfixheight = not side,
  } do
    vim.wo[state.win][opt] = val
  end
  state.last = nil
  M.refresh(vim.api.nvim_win_get_buf(src_win), src_win)
end

function M.close()
  if M.is_open() then
    local tab = vim.api.nvim_win_get_tabpage(state.win)
    if #vim.api.nvim_tabpage_list_wins(tab) > 1 then
      vim.api.nvim_win_close(state.win, true)
    elseif #vim.api.nvim_list_tabpages() > 1 then
      -- The pane is all that's left of its tab
      vim.cmd.tabclose(vim.api.nvim_tabpage_get_number(tab))
    else
      -- ...or of Neovim; fails harmlessly if something else has unsaved changes
      pcall(vim.cmd.quit)
    end
  end
  state.win = nil
  timer:stop()
end

function M.toggle()
  if M.is_open() then
    M.close()
  else
    M.open()
  end
end

---@param buf integer
function M.attach(buf)
  local group =
    vim.api.nvim_create_augroup('hol4goals_' .. buf, { clear = true })
  vim.api.nvim_create_autocmd(
    { 'CursorMoved', 'CursorMovedI', 'TextChanged', 'TextChangedI' },
    {
      group = group,
      buffer = buf,
      callback = M.schedule,
    }
  )
  vim.api.nvim_create_autocmd('BufWipeout', {
    group = group,
    buffer = buf,
    callback = function()
      state.costs[buf] = nil
      vim.api.nvim_del_augroup_by_id(group)
    end,
  })
end

-- Whether a window in the pane's tab other than `except` still shows a HOL
-- script
---@param except? integer
local function script_visible(except)
  for _, win in
    ipairs(
      vim.api.nvim_tabpage_list_wins(vim.api.nvim_win_get_tabpage(state.win))
    )
  do
    if
      win ~= except
      and vim.bo[vim.api.nvim_win_get_buf(win)].filetype == 'hol4script'
    then
      return true
    end
  end
  return false
end

local group = vim.api.nvim_create_augroup('hol4goals', { clear = true })

-- `:colorscheme` clears highlight groups, including these links
vim.api.nvim_create_autocmd('ColorScheme', { group = group, callback = set_hl })

-- Close the pane along with the last script it could be showing goals for
vim.api.nvim_create_autocmd({ 'WinClosed', 'BufDelete', 'BufWipeout' }, {
  group = group,
  callback = vim.schedule_wrap(function()
    if M.is_open() and not script_visible() then M.close() end
  end),
})

-- `:q` on the last script window: close the pane first, so Neovim quits rather
-- than leaving the pane as the only window
vim.api.nvim_create_autocmd('QuitPre', {
  group = group,
  callback = function()
    if M.is_open() and not script_visible(vim.api.nvim_get_current_win()) then
      M.close()
    end
  end,
})

vim.api.nvim_create_autocmd('WinResized', {
  group = group,
  callback = function()
    if
      not (
        M.is_open()
        and state.src
        and vim.tbl_contains(vim.v.event.windows, state.win)
      )
    then
      return
    end
    -- The same state again, broken to the new width
    state.last = nil
    reshow()
  end,
})

return M
