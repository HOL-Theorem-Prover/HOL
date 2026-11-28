-- What background proof checking has found. The server announces each change
-- on `$/proofStates` and never sends a snapshot, so it's accumulated here.
local M = {}

---@class hol4.Proof
---@field name string
---@field status string
---@field line integer 0-based, as the server last said
---@field mark? integer the extmark that follows the proof through edits

-- By name: the one identity that survives an edit moving the proof
---@type table<integer, table<string, hol4.Proof>>
local by_buf = {}

-- A proof that suspends ran and did what it said; the `Resume` blocks that
-- finish it off are entries of their own
local settled = { proved = true, suspended = true }
-- `cheated` means an edit reached it and the next pass will take it up. Any
-- other status is one to look at, including one this client doesn't know.
local outstanding = { checking = true, cheated = true }

-- What a status shows after the proof's first line: the `marks` option's
-- symbol for it, false for none. `cheated` shows nothing; anything that isn't
-- settled or outstanding went wrong, a timeout included.
local mark_hl = {
  proved = 'Hol4ProofOk',
  checking = 'Hol4ProofChecking',
  failed = 'Hol4ProofFailed',
}

---@param status string
---@return string[]?
local function mark_for(status)
  local kind = settled[status] and 'proved'
    or status == 'checking' and 'checking'
    or not outstanding[status] and 'failed'
  local symbol = kind and (require('hol4').opts.marks or {})[kind]
  if not symbol then return nil end
  return { symbol, mark_hl[kind] }
end

local function set_hl()
  vim.api.nvim_set_hl(
    0,
    'Hol4ProofOk',
    { link = 'DiagnosticOk', default = true }
  )
  vim.api.nvim_set_hl(
    0,
    'Hol4ProofChecking',
    { link = 'Comment', default = true }
  )
  vim.api.nvim_set_hl(
    0,
    'Hol4ProofFailed',
    { link = 'DiagnosticError', default = true }
  )
end
set_hl()

local ns = vim.api.nvim_create_namespace('hol4proofs')

-- Show `mark` (a `marks` entry, or nil for none) at the end of `line`,
-- reusing extmark `id`; returns the extmark's id, if there is one now
---@param buf integer
---@param id? integer
---@param line integer
---@param mark? string[]
---@return integer?
local function place(buf, id, line, mark)
  if not mark then
    if id then vim.api.nvim_buf_del_extmark(buf, ns, id) end
    return nil
  end
  line = math.min(line, vim.api.nvim_buf_line_count(buf) - 1)
  return vim.api.nvim_buf_set_extmark(buf, ns, line, 0, {
    id = id,
    -- `eol` already leaves a cell's gap
    virt_text = { { mark[1], mark[2] } },
    virt_text_pos = 'eol',
    invalidate = true,
  })
end

-- Where `proof` is now: its extmark has moved with any edits since the server
-- said
---@param buf integer
---@param proof hol4.Proof
local function line_of(buf, proof)
  if proof.mark then
    local pos = vim.api.nvim_buf_get_extmark_by_id(buf, ns, proof.mark, {})
    if pos[1] then return pos[1] end
  end
  return proof.line
end

local function changed()
  vim.api.nvim_exec_autocmds(
    'User',
    { pattern = 'Hol4ProofStates', modeline = false }
  )
  vim.cmd.redrawstatus { bang = true }
end

vim.api.nvim_create_autocmd('ColorScheme', {
  group = vim.api.nvim_create_augroup('hol4proofs', { clear = true }),
  callback = set_hl,
})

---@param params { uri: string, states: table[] }
function M.on_states(params)
  local buf = vim.uri_to_bufnr(params.uri)
  if not vim.api.nvim_buf_is_loaded(buf) then return end
  local proofs = by_buf[buf] or {}
  by_buf[buf] = proofs
  for _, state in ipairs(params.states) do
    if state.name and state.name ~= '' then
      local old = proofs[state.name]
      local proof = {
        name = state.name,
        status = state.status,
        line = state.pos and state.pos.line or 0,
      }
      proof.mark =
        place(buf, old and old.mark, proof.line, mark_for(proof.status))
      proofs[state.name] = proof
    end
  end
  changed()
end

-- Forget proofs that are no longer in the buffer. `declared` lists what it
-- still declares as of text `version`, absent when the server isn't checking
-- proofs; a list for older text would forget a proof the newer text has.
---@param params { uri: string, declared?: string[], version?: integer }
function M.on_compiled(params)
  local buf = vim.uri_to_bufnr(params.uri)
  local proofs = by_buf[buf]
  if not proofs or not vim.api.nvim_buf_is_loaded(buf) then return end
  local names
  if
    params.declared
    and (
      params.version == nil
      or params.version == vim.lsp.util.buf_versions[buf]
    )
  then
    names = {}
    for _, name in ipairs(params.declared) do
      names[name] = true
    end
  end
  local last = vim.api.nvim_buf_line_count(buf)
  local dropped = false
  for name, proof in pairs(proofs) do
    if proof.line >= last or (names and not names[name]) then
      place(buf, proof.mark, 0, nil)
      proofs[name] = nil
      dropped = true
    end
  end
  if dropped then changed() end
end

-- Ticks on proofs the goals pane found solved, while proof checking is off:
-- extmark ids by theorem name, by buffer
---@type table<integer, table<string, integer>>
local solved = {}

-- Forget `buf`'s proofs, or every buffer's
---@param buf? integer
function M.clear(buf)
  for b in
    pairs(
      buf and { [buf] = true } or vim.tbl_extend('force', {}, by_buf, solved)
    )
  do
    if vim.api.nvim_buf_is_valid(b) then
      vim.api.nvim_buf_clear_namespace(b, ns, 0, -1)
    end
    by_buf[b] = nil
    solved[b] = nil
  end
  changed()
end

-- An edit can break the proof it's in and any after it: drop their ticks
---@param buf integer
---@param first integer 0-based first line changed
local function edited(buf, first)
  local ticks = solved[buf]
  if not ticks then return end
  local above, above_row
  for name, id in pairs(ticks) do
    local row = vim.api.nvim_buf_get_extmark_by_id(buf, ns, id, {})[1]
    if not row or row >= first then
      place(buf, id, 0, nil)
      ticks[name] = nil
    elseif not above_row or row > above_row then
      above, above_row = name, row
    end
  end
  -- The nearest one above is the proof the edit is in, most likely
  if above then
    place(buf, ticks[above], 0, nil)
    ticks[above] = nil
  end
end

-- With proof checking off, the goals pane is all there is to go on: tick the
-- theorem a goal state at `row` (1-based) shows solved, and untick one that
-- went wrong
---@param buf integer
---@param row integer
---@param result table? a `$/hol/goalState` reply
function M.on_goal_state(buf, row, result)
  if require('hol4').check_proofs or not (result and result.theorem) then
    return
  end
  if result.status == 'pending' then return end
  local name = result.theorem
  local goals = result.goals ~= vim.NIL and result.goals or nil
  local failed = result.error ~= nil and result.error ~= vim.NIL
  local ticks = solved[buf]
  if not ticks then
    ticks = {}
    solved[buf] = ticks
    vim.api.nvim_buf_attach(buf, false, {
      on_lines = function(_, b, _, first)
        if not solved[b] then return true end
        vim.schedule(function()
          if vim.api.nvim_buf_is_valid(b) then edited(b, first) end
        end)
      end,
    })
  end
  if failed then
    ticks[name] = place(buf, ticks[name], 0, nil)
  elseif goals and #goals == 0 and not ticks[name] then
    -- The theorem's first line: the nearest line above naming it
    local lines = vim.api.nvim_buf_get_lines(buf, 0, row, false)
    local decl = '^%s*%a+%s+' .. vim.pesc(name) .. "%f[^%w_']"
    for r = #lines, 1, -1 do
      if lines[r]:match(decl) then
        ticks[name] = place(buf, nil, r - 1, mark_for('proved'))
        break
      end
    end
  end
end

---@param buf? integer
---@return { proved: integer, outstanding: integer, wrong: integer }
function M.counts(buf)
  local counts = { proved = 0, outstanding = 0, wrong = 0 }
  local proofs =
    by_buf[buf and buf ~= 0 and buf or vim.api.nvim_get_current_buf()]
  for _, proof in pairs(proofs or {}) do
    local bucket = settled[proof.status] and 'proved'
      or outstanding[proof.status] and 'outstanding'
      or 'wrong'
    counts[bucket] = counts[bucket] + 1
  end
  return counts
end

-- A tally for a statusline, e.g. `⊢12/14!1`: proved, out of how many, and how
-- many went wrong. Empty when there's nothing left to say.
---@param buf? integer
---@return string
function M.status(buf)
  local counts = M.counts(buf)
  if counts.outstanding == 0 and counts.wrong == 0 then return '' end
  local total = counts.proved + counts.outstanding + counts.wrong
  local wrong = counts.wrong > 0 and '!' .. counts.wrong or ''
  return ('⊢%d/%d%s'):format(counts.proved, total, wrong)
end

---@param proof hol4.Proof
local function describe(proof)
  if proof.status == 'cheated' then return 'not checked' end
  if proof.status == 'timedout' then return 'not checked (timed out)' end
  return proof.status
end

-- Move to the next (`dir` 1) or previous (`dir` -1) proof that isn't settled,
-- wrapping around the file
---@param dir 1|-1
function M.jump(dir)
  local list = {}
  local buf = vim.api.nvim_get_current_buf()
  for _, proof in pairs(by_buf[buf] or {}) do
    if not settled[proof.status] then
      table.insert(
        list,
        { name = proof.name, status = proof.status, line = line_of(buf, proof) }
      )
    end
  end
  if #list == 0 then
    local checking = require('hol4').check_proofs
    vim.notify(
      checking and 'hol4: no outstanding proofs'
        or 'hol4: proof checking is off (`:Hol checkproofs on`)'
    )
    return
  end
  table.sort(list, function(a, b) return a.line < b.line end)

  local here = vim.api.nvim_win_get_cursor(0)[1] - 1
  local target = dir > 0 and list[1] or list[#list]
  for i = dir > 0 and 1 or #list, dir > 0 and #list or 1, dir do
    local line = list[i].line
    if (dir > 0 and line > here) or (dir < 0 and line < here) then
      target = list[i]
      break
    end
  end
  vim.cmd("normal! m'")
  vim.api.nvim_win_set_cursor(0, { target.line + 1, 0 })
  vim.cmd('normal! ^')
  vim.notify(
    ('hol4: %s is %s (%d to go)'):format(target.name, describe(target), #list)
  )
end

return M
