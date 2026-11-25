-- Theorem search through `$/hol/search`: a live Snacks or Telescope picker, or
-- with neither a prompt and then `vim.ui.select`, which can't update as you
-- type.
local M = {}

---@alias hol4.SearchMode 'name'|'term'

---@class hol4.Query
---@field mode hol4.SearchMode
---@field limit integer
---@field title string

-- Split the prompt into the server's selectors, which narrow each other.
-- `'thy'` picks a theory, and ``` ``term`` ``` a term pattern, by either
-- mode. By name, each other word is a fragment of the name; by term, `"name"`
-- is, and whatever else is left over is one term pattern. An unclosed quote
-- is closed at the end, so results show up while typing it.
---@param input string
---@param mode hol4.SearchMode
---@return string[]
local function selectors(input, mode)
  local sels, rest = {}, {}
  local i = 1
  while i <= #input do
    local c = input:sub(i, i)
    -- Only at the start of a word, so a primed variable (x') stays part of a
    -- term
    local word_start = i == 1 or input:sub(i - 1, i - 1):match('%s')
    if input:sub(i, i + 1) == '``' then
      local j = input:find('``', i + 2, true) or #input + 1
      local body = vim.trim(input:sub(i + 2, j - 1))
      if body ~= '' then table.insert(sels, body) end
      i = j + 2
    elseif (c == "'" or c == '"') and word_start then
      local j = input:find(c, i + 1, true) or #input + 1
      local body = input:sub(i + 1, j - 1)
      if body ~= '' then table.insert(sels, c .. body .. c) end
      i = j + 1
    elseif mode == 'name' and c:match('%S') then
      local j = (input:find('%s', i) or #input + 1) - 1
      table.insert(sels, '"' .. input:sub(i, j) .. '"')
      i = j + 1
    else
      table.insert(rest, c)
      i = i + 1
    end
  end
  local term = vim.trim(table.concat(rest))
  if term ~= '' then table.insert(sels, term) end
  return sels
end

M._selectors = selectors

---@class hol4.SearchHit
---@field theory string
---@field name string
---@field class string
---@field statement string statement on one line
---@field file? string where it was proved, when the theory recorded it
---@field line? integer 1-based

---@param h table a `$/hol/search` result
---@return hol4.SearchHit
local function hit(h)
  return {
    theory = h.theory,
    name = h.name,
    class = h.class,
    statement = vim.trim(h.statement or ''):gsub('%s*\n%s*', ' '),
    file = h.uri and vim.uri_to_fname(h.uri) or nil,
    line = h.line,
  }
end

---@param client vim.lsp.Client
---@param buf integer
---@param prompt string
---@param q hol4.Query
---@param cb fun(hits: hol4.SearchHit[])
---@return fun()? cancel
local function search(client, buf, prompt, q, cb)
  local sels = selectors(prompt, q.mode)
  if #sels == 0 or client:is_stopped() then return cb {} end
  local ok, id = client:request(
    '$/hol/search',
    { selectors = sels, limit = q.limit },
    function(err, result) cb(vim.tbl_map(hit, (not err and result) or {})) end,
    buf
  )
  return ok and function() client:cancel_request(id) end or nil
end

---@param client vim.lsp.Client
---@param buf integer
---@param q hol4.Query
local function snacks(client, buf, q)
  Snacks.picker.pick {
    title = q.title,
    live = true,
    supports_live = true,
    finder = function(_, ctx)
      ---@async
      return function(cb)
        local async = require('snacks.picker.util.async').running()
        local hits
        -- The finder runs in a fast event, where client:request isn't allowed
        vim.schedule(function()
          search(client, buf, ctx.filter.search, q, function(h)
            hits = h
            async:resume()
          end)
        end)
        while hits == nil do
          async:suspend()
        end
        for _, h in ipairs(hits) do
          cb {
            text = h.theory .. '$' .. h.name .. ' ' .. h.statement,
            hit = h,
            file = h.file,
            pos = h.line and { h.line, 0 } or nil,
            -- No source recorded (e.g. a theory from sigobj): show the
            -- statement instead
            preview = not h.file and { text = h.statement } or nil,
          }
        end
      end
    end,
    format = function(item)
      return {
        { item.hit.theory .. '$', 'Comment' },
        { item.hit.name, 'Function' },
        { ' ' },
        { item.hit.statement, 'Normal' },
      }
    end,
    preview = function(ctx)
      if ctx.item.file then return Snacks.picker.preview.file(ctx) end
      return Snacks.picker.preview.preview(ctx)
    end,
  }
end

---@param client vim.lsp.Client
---@param buf integer
---@param q hol4.Query
local function telescope(client, buf, q)
  local actions = require('telescope.actions')
  local action_state = require('telescope.actions.state')
  local conf = require('telescope.config').values
  local finders = require('telescope.finders')
  local pickers = require('telescope.pickers')
  local previewers = require('telescope.previewers')
  local sorters = require('telescope.sorters')
  local channel = require('plenary.async.control').channel

  local cancel = function() end
  pickers
    .new({}, {
      prompt_title = q.title,
      -- Called inside a plenary coroutine, as for Telescope's own dynamic
      -- workspace symbols
      finder = finders.new_dynamic {
        fn = function(prompt)
          local tx, rx = channel.oneshot()
          cancel()
          cancel = search(client, buf, prompt or '', q, tx) or function() end
          return rx()
        end,
        entry_maker = function(h)
          local prefix = h.theory .. '$'
          return {
            value = h,
            ordinal = prefix .. h.name .. ' ' .. h.statement,
            display = function()
              return prefix .. h.name .. ' ' .. h.statement,
                {
                  { { 0, #prefix }, 'Comment' },
                  { { #prefix, #prefix + #h.name }, 'Function' },
                }
            end,
            filename = h.file,
            lnum = h.line,
          }
        end,
      },
      -- The server has already matched; fuzzy re-filtering would drop
      -- term-pattern hits
      sorter = sorters.highlighter_only {},
      previewer = previewers.new_buffer_previewer {
        title = 'HOL theorem',
        get_buffer_by_name = function(_, entry) return entry.filename end,
        define_preview = function(self, entry)
          if not entry.filename then
            vim.api.nvim_buf_set_lines(
              self.state.bufnr,
              0,
              -1,
              false,
              { entry.value.statement }
            )
            return
          end
          conf.buffer_previewer_maker(entry.filename, self.state.bufnr, {
            bufname = self.state.bufname,
            winid = self.state.winid,
            callback = function()
              if
                not (entry.lnum and vim.api.nvim_win_is_valid(self.state.winid))
              then
                return
              end
              pcall(
                vim.api.nvim_win_set_cursor,
                self.state.winid,
                { entry.lnum, 0 }
              )
              vim.api.nvim_win_call(
                self.state.winid,
                function() vim.cmd('normal! zt') end
              )
            end,
          })
        end,
      },
      attach_mappings = function(prompt_bufnr)
        -- Nowhere to jump for a theorem without a recorded source
        actions.select_default:replace_if(function()
          local entry = action_state.get_selected_entry()
          return entry ~= nil and entry.filename == nil
        end, function() actions.close(prompt_bufnr) end)
        return true
      end,
    })
    :find()
end

---@param client vim.lsp.Client
---@param buf integer
---@param q hol4.Query
local function select(client, buf, q)
  vim.ui.input({ prompt = q.title .. ': ' }, function(prompt)
    if not prompt or vim.trim(prompt) == '' then return end
    search(client, buf, prompt, q, function(hits)
      if #hits == 0 then
        vim.notify('hol4: no theorems found for ' .. prompt)
        return
      end
      vim.ui.select(hits, {
        prompt = q.title,
        format_item = function(h)
          return h.theory .. '$' .. h.name .. ' ' .. h.statement
        end,
      }, function(h)
        if not h then return end
        if not h.file then
          -- No source recorded (e.g. a theory from sigobj)
          vim.notify(h.theory .. '$' .. h.name .. ': ' .. h.statement)
          return
        end
        vim.cmd.edit(vim.fn.fnameescape(h.file))
        if h.line then pcall(vim.api.nvim_win_set_cursor, 0, { h.line, 0 }) end
      end)
    end)
  end)
end

---@class hol4.SearchOpts
--- `'name'`: words are fragments of the theorem's name. `'term'`: the text is
--- a term pattern. (default: `'name'`)
---@field mode? hol4.SearchMode
--- Most results to ask for (default: the `search.limit` option)
---@field limit? integer
---@field picker? 'snacks'|'telescope'|'select'

---@param opts? hol4.SearchOpts
function M.open(opts)
  opts = opts or {}
  local mode = opts.mode or 'name'
  local client = vim.lsp.get_clients({ bufnr = 0, name = 'hol' })[1]
    or vim.lsp.get_clients({ name = 'hol' })[1]
  if not client then
    vim.notify('hol4: no server running', vim.log.levels.WARN)
    return
  end
  local buf = assert(next(client.attached_buffers))
  local q = {
    mode = mode,
    limit = opts.limit or require('hol4').opts.search.limit or 200,
    title = mode == 'term' and 'HOL theorems by term' or 'HOL theorems by name',
  }

  local picker = opts.picker or require('hol4').opts.picker
  if not picker then
    picker = (rawget(_G, 'Snacks') and Snacks.picker) and 'snacks'
      or pcall(require, 'telescope') and 'telescope'
      or 'select'
  end
  if picker == 'snacks' then
    snacks(client, buf, q)
  elseif picker == 'telescope' then
    telescope(client, buf, q)
  else
    select(client, buf, q)
  end
end

-- Search by name: ``` ``term`` ``` for a term pattern
function M.by_name() M.open { mode = 'name' } end

-- Search by term pattern: `"name"` for a fragment of the name
function M.by_term() M.open { mode = 'term' } end

return M
