-- The eval window: what the last eval printed, in a float in the middle of
-- the screen, entered as it opens. `q` or `<Esc>` closes it and goes back to
-- the script; so does entering insert mode in a script, or closing it.
local M = {}

local ns = vim.api.nvim_create_namespace('hol4eval')

---@return hol4.EvalOpts
local function opts() return require('hol4').opts.eval or {} end

---@type { buf?: integer, win?: integer, anchor?: integer }
local state = {}

function M.is_open()
  return state.win ~= nil and vim.api.nvim_win_is_valid(state.win)
end

-- Close, and go back to the script if the float had the cursor
function M.close()
  if M.is_open() then
    local inside = vim.api.nvim_get_current_win() == state.win
    vim.api.nvim_win_close(state.win, true)
    if inside and state.anchor and vim.api.nvim_win_is_valid(state.anchor) then
      vim.api.nvim_set_current_win(state.anchor)
    end
  end
  state.win = nil
end

local function get_buf()
  if state.buf and vim.api.nvim_buf_is_valid(state.buf) then
    return state.buf
  end
  local buf = vim.api.nvim_create_buf(false, true)
  vim.api.nvim_buf_set_name(buf, 'hol4://eval')
  -- Output is mostly Poly printing values, which reads as SML
  vim.bo[buf].filetype = 'sml'
  vim.bo[buf].bufhidden = 'hide'
  vim.bo[buf].modifiable = false
  local hol = require('hol4')
  hol._map(buf, (hol.opts.eval.keys or {}).close, M.close, 'Close eval')
  state.buf = buf
  return buf
end

-- Size the float to `lines` and centre it; a new one is entered unless
-- `enter` is false
---@param lines string[]
---@param title string
---@param enter? boolean
local function open(lines, title, enter)
  local o = opts()
  local room = vim.o.columns - 8
  local width = vim.fn.strdisplaywidth(title) + 2
  for _, line in ipairs(lines) do
    width = math.max(width, vim.fn.strdisplaywidth(line))
  end
  width = math.max(math.min(width, o.max_width or 100, room), 20)
  local height = 0
  for _, line in ipairs(lines) do
    height = height
      + math.max(1, math.ceil(vim.fn.strdisplaywidth(line) / width))
  end
  height = math.max(1, math.min(height, o.max_height or 15, vim.o.lines - 6))
  local config = {
    relative = 'editor',
    row = math.floor((vim.o.lines - height) / 2) - 1,
    col = math.floor((vim.o.columns - width) / 2),
    width = width,
    height = height,
    border = o.border or 'rounded',
    title = ' ' .. title .. ' ',
    title_pos = 'center',
  }
  if M.is_open() then
    vim.api.nvim_win_set_config(state.win, config)
    return
  end
  config.style = 'minimal'
  enter = enter ~= false and o.enter ~= false
  state.win = vim.api.nvim_open_win(get_buf(), enter, config)
  vim.wo[state.win].wrap = true
  vim.wo[state.win].linebreak = true
  vim.wo[state.win].winfixbuf = true
end

---@param code string
local function title(code)
  local text = vim.trim(code:gsub('%s+', ' '))
  if vim.fn.strchars(text) > 60 then
    text = vim.fn.strcharpart(text, 0, 59) .. '…'
  end
  return text
end

-- Say that `code` is running, keeping what the last eval printed meanwhile
---@param code string
function M.pending(code)
  -- Called as the eval is sent, from the script's window
  local here = vim.api.nvim_get_current_win()
  if here ~= state.win then state.anchor = here end
  local lines = M.is_open()
      and vim.api.nvim_buf_get_lines(get_buf(), 0, -1, false)
    or { '' }
  if not M.is_open() then
    local buf = get_buf()
    vim.bo[buf].modifiable = true
    vim.api.nvim_buf_set_lines(buf, 0, -1, false, lines)
    vim.bo[buf].modifiable = false
    vim.api.nvim_buf_clear_namespace(buf, ns, 0, -1)
  end
  open(lines, title(code) .. ' (running…)')
end

---@param code string
---@param lines hol4.Line[]
function M.show(code, lines)
  if #lines == 0 then lines = { { text = '(no output)' } } end
  local buf = get_buf()
  local text = vim.tbl_map(function(l) return l.text end, lines)
  vim.bo[buf].modifiable = true
  vim.api.nvim_buf_set_lines(buf, 0, -1, false, text)
  vim.bo[buf].modifiable = false
  vim.api.nvim_buf_clear_namespace(buf, ns, 0, -1)
  for row, line in ipairs(lines) do
    if line.hl then
      -- An error's text isn't SML: cover the highlighting of output
      vim.api.nvim_buf_set_extmark(buf, ns, row - 1, 0, {
        end_col = #line.text,
        hl_group = 'Hol4EvalText',
        priority = 150,
      })
      for _, h in ipairs(line.hl) do
        vim.api.nvim_buf_set_extmark(buf, ns, row - 1, h[1], {
          end_col = h[2],
          hl_group = h[3],
          priority = 151,
        })
      end
    end
  end
  -- Reopened if closed while it ran; but not into the middle of typing
  open(text, title(code), not vim.fn.mode():match('^[iR]'))
  vim.api.nvim_win_set_cursor(state.win, { 1, 0 })
end

local group = vim.api.nvim_create_augroup('hol4eval', { clear = true })

-- Back to editing: the output has had its look
vim.api.nvim_create_autocmd('InsertEnter', {
  group = group,
  callback = function(ev)
    if vim.bo[ev.buf].filetype == 'hol4script' then M.close() end
  end,
})

-- Go with the script's window; `:q` there would otherwise refuse to leave
-- only a float behind
vim.api.nvim_create_autocmd({ 'WinClosed', 'QuitPre' }, {
  group = group,
  callback = function(ev)
    local win = ev.event == 'WinClosed' and tonumber(ev.match)
      or vim.api.nvim_get_current_win()
    if not (M.is_open() and win == state.anchor) then return end
    -- No closing windows while one is being closed
    if ev.event == 'WinClosed' then
      vim.schedule(M.close)
    else
      M.close()
    end
  end,
})

return M
