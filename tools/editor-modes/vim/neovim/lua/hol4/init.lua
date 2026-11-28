-- HOL4 through its own language server, `bin/hol lsp` (tools-poly/lsp).
local M = {}
local goals = require('hol4.goals')
local proofs = require('hol4.proofs')
local output = require('hol4.output')
local report = require('hol4.report')

-- This plugin lives in tools/editor-modes/vim/neovim of a HOL checkout
local holdir = vim.fs.normalize(
  vim.fs.joinpath(debug.getinfo(1, 'S').source:sub(2), '../../../../../../..')
)
local own_hol = vim.fs.joinpath(holdir, 'bin', 'hol')

---@class hol4.Opts
--- `hol` for a directory no `Holmake` has built yet (default: the `bin/hol`
--- of the HOL checkout this plugin is in, else `hol` on PATH)
---@field hol? string
--- Replay every proof in the background and mark failures (default: false)
---@field check_proofs? boolean
--- Goals pane follows the cursor (default: true)
---@field goals_follow? boolean
--- How long a goal-state walk may run before it is cut off, in ms. A tactic
--- slower than this reports an error rather than a state (default: the
--- server's, 1500)
---@field walk_budget_ms? integer
--- How long proof checking lets one proof run before calling it timed out,
--- in ms; 0 for no limit (default: the server's, 120000)
---@field proof_timeout_ms? integer
--- Theorem search picker (default: Snacks, then Telescope, then vim.ui.select)
---@field picker? 'snacks'|'telescope'|'select'
--- What goes after a theorem's first line: `proved` once its proof passes,
--- `checking` while it's checked, `failed` once it fails or times out; false
--- for nothing
---@field marks? hol4.Marks
--- Where the goals pane opens, and how big
---@field goals? hol4.GoalsOpts
--- The eval float
---@field eval? hol4.EvalOpts
---@field search? { limit?: integer } most results to ask for (default: 200)
--- Width hovers are laid out to, in columns (default: the server's, 100)
---@field hover_width? integer

---@class hol4.Marks
---@field proved? string|false
---@field checking? string|false
---@field failed? string|false

---@class hol4.GoalsOpts
--- `'right'`, `'below'`, or `'auto'`: right of a window at least 160 columns
--- wide, else below (default: `'auto'`)
---@field position? 'auto'|'right'|'below'
--- Columns when on the right (default: a third of the window)
---@field width? integer
--- Lines when below (default: 15)
---@field height? integer
--- The pane's own keys: `info` shows the type of the symbol under the cursor
--- (default: `'K'`), `close` closes the pane (default: `'q'`)
---@field keys? { info?: hol4.Keys, close?: hol4.Keys }

---@class hol4.EvalOpts
---@field border? string|string[] (default: `'rounded'`)
---@field max_width? integer (default: 100)
---@field max_height? integer (default: 15)
--- Move the cursor into it as it opens (default: true)
---@field enter? boolean
--- The float's own keys: `close` (default: `{ 'q', '<Esc>' }`)
---@field keys? { close?: hol4.Keys }

--- A key, several, or false for none
---@alias hol4.Keys string|string[]|false

-- Map `keys` (a `hol4.Keys`) to `rhs` in `buf`
---@param buf integer
---@param keys? hol4.Keys
---@param rhs function
---@param desc string
function M._map(buf, keys, rhs, desc)
  if not keys then return end
  for _, lhs in ipairs(type(keys) == 'table' and keys or { keys }) do
    vim.keymap.set('n', lhs, rhs, { buffer = buf, desc = desc })
  end
end

local defaults = {
  marks = { proved = '✓', checking = '⋯', failed = '✗' },
  goals = {
    position = 'auto',
    height = 15,
    keys = { info = 'K', close = 'q' },
  },
  eval = {
    border = 'rounded',
    max_width = 100,
    max_height = 15,
    enter = true,
    keys = { close = { 'q', '<Esc>' } },
  },
  search = { limit = 200 },
  hol = vim.fn.executable(own_hol) == 1 and own_hol or 'hol',
  check_proofs = false,
  goals_follow = true,
}

M.opts = vim.deepcopy(defaults)
M.check_proofs = M.opts.check_proofs
M.did_setup = false

-- The `hol` that last built `dir`, as hol-mode.el's
-- hol--find-alternate-executable does
local function hol_for(dir)
  local f = io.open(dir .. '/.hol/make-deps/lastmaker')
  local line = f and f:read('*l')
  if f then f:close() end
  local hol = line and vim.fs.joinpath(vim.fs.dirname(line), 'hol')
  return (hol and vim.fn.executable(hol) == 1) and hol or M.opts.hol
end

M._hol_for = hol_for

-- The Vim mode's syntax file, one directory above this plugin, if it's there
---@return string?
function M._vim_mode_syntax()
  local path = vim.fs.joinpath(holdir, 'tools/editor-modes/vim/hol4script.vim')
  return vim.uv.fs_stat(path) and path or nil
end

---@param bufnr? integer
---@return vim.lsp.Client?
function M.client(bufnr)
  local client = vim.lsp.get_clients({ bufnr = bufnr or 0, name = 'hol' })[1]
  if not client then
    vim.notify('hol4: no server for this buffer', vim.log.levels.WARN)
  end
  return client
end

-- The text of a selection and where it starts ({row, col}: 1-based row, byte
-- col). With `marks`, the last visual selection (for a command's range);
-- otherwise the current one, which this ends.
---@param marks? boolean
---@return string text, integer[] start
local function selection(marks)
  local a = vim.fn.getpos(marks and "'<" or 'v')
  local b = vim.fn.getpos(marks and "'>" or '.')
  local mode = marks and vim.fn.visualmode() or vim.fn.mode()
  local lines = vim.fn.getregion(a, b, { type = mode })
  if a[2] > b[2] or (a[2] == b[2] and a[3] > b[3]) then a = b end
  if not marks then vim.api.nvim_feedkeys(vim.keycode('<Esc>'), 'nx', false) end
  return table.concat(lines, '\n'), { a[2], a[3] - 1 }
end
M._selection = selection

-- Eval ------------------------------------------------------------------------

---@type { client: vim.lsp.Client, id: integer, cancelled?: boolean }?
local last_eval

-- Evaluate `code` in the server's session, scoped to `pos` ({row, col}: 1-based
-- row, byte col; default: the cursor)
---@param code string
---@param bufnr? integer
---@param pos? integer[]
function M.eval(code, bufnr, pos)
  bufnr = bufnr or vim.api.nvim_get_current_buf()
  local client = M.client(bufnr)
  if not client or code:match('^%s*$') then return end
  pos = pos or vim.api.nvim_win_get_cursor(0)
  local position = vim.lsp.util.make_given_range_params(
    pos,
    pos,
    bufnr,
    client.offset_encoding
  ).range.start
  local req = { client = client }
  local ok, id = client:request('$/eval', {
    uri = vim.uri_from_bufnr(bufnr),
    code = code,
    position = position,
  }, function(err, result)
    if last_eval == req then last_eval = nil end
    if err then
      -- The server answers a cancelled request as an "Interrupt" error
      output.show(code, {
        { text = req.cancelled and '[cancelled]' or 'error: ' .. err.message },
      })
    else
      output.show(code, report.format(result or {}, pos))
    end
  end, bufnr)
  if ok and id then
    req.id = id
    last_eval = req
    output.pending(code)
  end
end

-- Evaluate the cursor's line
function M.eval_line()
  local row = vim.api.nvim_win_get_cursor(0)[1]
  M.eval(vim.api.nvim_get_current_line(), nil, { row, 0 })
end

-- Evaluate the visual selection (call from a visual-mode mapping)
function M.eval_visual()
  local code, pos = selection()
  M.eval(code, nil, pos)
end

function M.eval_prompt()
  local bufnr = vim.api.nvim_get_current_buf()
  local pos = vim.api.nvim_win_get_cursor(0)
  vim.ui.input({ prompt = 'HOL eval: ' }, function(code)
    if code then M.eval(code, bufnr, pos) end
  end)
end

-- Cancel the running eval
function M.cancel()
  if not last_eval then return end
  last_eval.cancelled = true
  last_eval.client:cancel_request(last_eval.id)
end

-- Server control --------------------------------------------------------------

-- Recompile after a missing ancestor theory has been built (one already
-- loaded needs restart())
function M.retry_compile()
  local client = M.client()
  if not client then return end
  client:notify(
    '$/hol/retryCompile',
    { textDocument = { uri = vim.uri_from_bufnr(0) } }
  )
end

-- Restart this buffer's server only. `:lsp restart` reuses by root dir, which
-- would hand the buffer to another script's server in the same directory.
function M.restart()
  local bufnr = vim.api.nvim_get_current_buf()
  local old = vim.lsp.get_clients { bufnr = bufnr, name = 'hol' }
  for _, client in ipairs(old) do
    client:stop()
  end
  local function start()
    for _, client in ipairs(old) do
      if not client:is_stopped() then return vim.defer_fn(start, 50) end
    end
    if not vim.api.nvim_buf_is_valid(bufnr) then return end
    local config = vim.deepcopy(vim.lsp.config.hol)
    config.root_dir = vim.fs.dirname(vim.api.nvim_buf_get_name(bufnr))
    vim.lsp.start(config, { bufnr = bufnr, reuse_client = config.reuse_client })
  end
  start()
end

---@param on boolean
function M.set_check_proofs(on)
  M.check_proofs = on
  -- Off: what checking found is stale. On: so are the goal pane's ticks.
  proofs.clear()
  for _, client in ipairs(vim.lsp.get_clients { name = 'hol' }) do
    client:request('$/setConfig', { checkProofs = on }, function() end)
  end
end

---@param on boolean
function M.set_goals_follow(on) goals.follow = on end

-- A tally of proof checking for a statusline, e.g. `⊢12/14!1`: proved, out of
-- how many, and how many went wrong. Empty when there's nothing left to say.
---@param buf? integer
---@return string
function M.status(buf) return proofs.status(buf) end

-- Move to the next proof that's outstanding or went wrong
function M.next_proof() proofs.jump(1) end

-- Move to the previous proof that's outstanding or went wrong
function M.prev_proof() proofs.jump(-1) end

-- Setup -----------------------------------------------------------------------

---@param buf integer
local function on_filetype(buf) goals.attach(buf) end

---@param opts? hol4.Opts
function M.setup(opts)
  if vim.fn.has('nvim-0.12') == 0 then
    vim.notify('hol4: needs Neovim 0.12 or later', vim.log.levels.ERROR)
    return
  end
  M.opts = vim.tbl_deep_extend('force', defaults, opts or {})
  -- A list of keys replaces the default's rather than merging into it
  for _, pane in ipairs { 'goals', 'eval' } do
    for name, keys in pairs(opts and opts[pane] and opts[pane].keys or {}) do
      M.opts[pane].keys[name] = keys
    end
  end
  M.check_proofs = M.opts.check_proofs
  goals.follow = M.opts.goals_follow
  M.did_setup = true

  local group = vim.api.nvim_create_augroup('hol4', { clear = true })
  vim.api.nvim_create_autocmd('FileType', {
    pattern = 'hol4script',
    group = group,
    callback = function(ev) on_filetype(ev.buf) end,
  })

  vim.lsp.config('hol', {
    cmd = function(dispatchers, config)
      return vim.lsp.rpc.start(
        { hol_for(config.root_dir), 'lsp' },
        dispatchers,
        { cwd = config.root_dir }
      )
    end,
    filetypes = { 'hol4script' },
    root_dir = function(bufnr, on_dir)
      on_dir(vim.fs.dirname(vim.api.nvim_buf_get_name(bufnr)))
    end,
    -- One server per buffer: a server can't be re-aimed at a second file, so
    -- only "reuse" the client this buffer already has.
    reuse_client = function(client, _, bufnr)
      return client.name == 'hol'
        and not client:is_stopped()
        and client.attached_buffers[bufnr] ~= nil
    end,
    on_init = function(client)
      local config = {
        checkProofs = M.check_proofs or nil,
        walkBudgetMs = M.opts.walk_budget_ms,
        proofTimeoutMs = M.opts.proof_timeout_ms,
        hoverWidth = M.opts.hover_width,
      }
      if next(config) then
        client:request('$/setConfig', config, function() end)
      end
    end,
    handlers = {
      ['$/compileCompleted'] = function(_, params)
        goals.on_compiled(params.uri)
        proofs.on_compiled(params)
      end,
      -- Checking off cancels the pool, whose last words shouldn't start a tally
      ['$/proofStates'] = function(_, params)
        if M.check_proofs then proofs.on_states(params) end
      end,
      -- The server's copy of the text has drifted from ours: send it all
      ['$/hol/desync'] = function(_, params, ctx)
        local bufnr = vim.uri_to_bufnr(params.uri)
        local client = vim.lsp.get_client_by_id(ctx.client_id)
        if not (client and vim.api.nvim_buf_is_loaded(bufnr)) then return end
        local lines = vim.api.nvim_buf_get_lines(bufnr, 0, -1, false)
        local text = table.concat(lines, '\n')
        if vim.bo[bufnr].eol then text = text .. '\n' end
        client:notify('textDocument/didChange', {
          textDocument = {
            uri = params.uri,
            version = vim.lsp.util.buf_versions[bufnr],
          },
          contentChanges = { { text = text } },
        })
      end,
    },
  })
  vim.lsp.enable('hol')

  -- Each server holds a HOL heap, so stop it once its buffer is gone.
  vim.api.nvim_create_autocmd('LspDetach', {
    group = group,
    callback = function(ev)
      local client = vim.lsp.get_client_by_id(ev.data.client_id)
      if not client or client.name ~= 'hol' then return end
      proofs.clear(ev.buf)
      vim.schedule(function()
        if not client:is_stopped() and next(client.attached_buffers) == nil then
          client:stop()
        end
      end)
    end,
  })

  -- Scripts already open, e.g. the one whose FileType loaded the plugin
  for _, buf in ipairs(vim.api.nvim_list_bufs()) do
    if
      vim.api.nvim_buf_is_loaded(buf) and vim.bo[buf].filetype == 'hol4script'
    then
      on_filetype(buf)
    end
  end
end

return M
