if vim.g.loaded_hol4 then return end
vim.g.loaded_hol4 = true

local function hol() return require('hol4') end
local function goals() return require('hol4.goals') end

-- `on`, `off` or (no argument) the opposite of `current`
---@param arg? string
---@param current boolean
local function switch(arg, current)
  if arg == nil or arg == 'toggle' then return not current end
  if arg == 'on' or arg == 'off' then return arg == 'on' end
  error('expected on, off or toggle', 0)
end

-- What a command acts on: its arguments, else the range's text (with where
-- it starts), else nothing (prompt for it)
---@param cmd vim.api.keyset.create_user_command.command_args
---@param args string[]
local function code_of(cmd, args)
  if #args > 0 then return table.concat(args, ' ') end
  if cmd.range > 0 then return hol()._selection(true) end
end

---@type table<string, fun(args: string[], cmd: table)>
local subcommands = {
  goals = function() goals().toggle() end,
  refresh = function() goals().refresh() end,
  eval = function(args, cmd)
    local code, pos = code_of(cmd, args)
    if code then
      hol().eval(code, nil, pos)
    else
      hol().eval_prompt()
    end
  end,
  search = function(args)
    require('hol4.search').open { mode = args[1] == 'term' and 'term' or 'name' }
  end,
  cancel = function() hol().cancel() end,
  retry = function() hol().retry_compile() end,
  restart = function() hol().restart() end,
  nextproof = function() hol().next_proof() end,
  prevproof = function() hol().prev_proof() end,
  checkproofs = function(args)
    hol().set_check_proofs(switch(args[1], hol().check_proofs))
  end,
  follow = function(args)
    hol().set_goals_follow(switch(args[1], goals().follow))
  end,
}

-- What each subcommand's argument can be
local arguments = {
  checkproofs = { 'on', 'off', 'toggle' },
  follow = { 'on', 'off', 'toggle' },
  search = { 'name', 'term' },
}

vim.api.nvim_create_user_command('Hol', function(cmd)
  local sub = table.remove(cmd.fargs, 1)
  local run = subcommands[sub]
  if not run then
    vim.notify('Hol: unknown subcommand ' .. sub, vim.log.levels.ERROR)
    return
  end
  local ok, err = pcall(run, cmd.fargs, cmd)
  if not ok then
    vim.notify('Hol ' .. sub .. ': ' .. err, vim.log.levels.ERROR)
  end
end, {
  nargs = '+',
  range = true,
  desc = 'HOL4: goals, eval, search, cancel, retry, restart, …',
  complete = function(lead, line)
    local words = vim.split(line:gsub('^%S*%s*', ''), '%s+')
    local list = {}
    if #words <= 1 then
      list = vim.tbl_keys(subcommands)
      table.sort(list)
    elseif #words == 2 and arguments[words[1]] then
      list = arguments[words[1]]
    end
    return vim.tbl_filter(function(s) return vim.startswith(s, lead) end, list)
  end,
})

-- Set up with the defaults for a user who doesn't call setup()
vim.api.nvim_create_autocmd('FileType', {
  pattern = 'hol4script',
  group = vim.api.nvim_create_augroup('hol4_autosetup', { clear = true }),
  once = true,
  callback = function()
    if not hol().did_setup then hol().setup() end
  end,
})
