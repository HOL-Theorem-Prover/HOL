-- `:checkhealth hol4`
local M = {}
local health = vim.health

-- What goes into `bin/hol` when configure compiles it. `bin/build` doesn't
-- check the tools-poly/lsp ones, so a pull can leave `bin/hol` behind them.
local compiled_in = {
  'tools-poly/hol.ML',
  'tools-poly/lsp/LSPExtension.sig',
  'tools-poly/lsp/LSPExtension.sml',
  'tools-poly/lsp/holide.ML',
  'tools-poly/lsp/lsp_namespace.ML',
  'tools-poly/lsp/server.ML',
}

---@param path string
---@return integer? seconds
local function mtime(path)
  local stat = vim.uv.fs_stat(path)
  return stat and stat.mtime.sec
end

-- The directory of the HOL script being checked, if `:checkhealth` was run
-- from one. Its Holmakefile decides the heap, and its build the `hol`.
---@return string?
local function script_dir()
  -- `:checkhealth` opens its report in a new tab, leaving the script in the
  -- alternate buffer
  local alt = vim.fn.bufnr('#')
  if alt > 0 and vim.bo[alt].filetype == 'hol4script' then
    return vim.fs.dirname(vim.api.nvim_buf_get_name(alt))
  end
end

---@param hol string absolute path of a `hol` executable
local function check_build(hol)
  local holdir = vim.fs.dirname(vim.fs.dirname(vim.uv.fs_realpath(hol) or hol))
  local built = mtime(hol)
  local newer = {}
  for _, rel in ipairs(compiled_in) do
    local src = mtime(vim.fs.joinpath(holdir, rel))
    if src and built and src > built then table.insert(newer, rel) end
  end
  if #newer > 0 then
    health.warn(
      '`' .. hol .. '` is older than: ' .. table.concat(newer, ', '),
      {
        'If those sources really changed, the goals pane will stop working.',
        'In '
          .. holdir
          .. ': `poly < tools/smart-configure.sml`, then `bin/build`',
      }
    )
  end

  local heap = vim.fs.joinpath(holdir, 'bin', 'hol.state')
  local heap_time = mtime(heap)
  if not heap_time then
    health.error('No heap at ' .. heap, { 'Run `bin/build` in ' .. holdir })
  elseif built and heap_time < built then
    health.warn('`' .. heap .. '` is older than `' .. hol .. '`', {
      'A heap only loads into the executable that made it: run `bin/build`',
    })
  else
    health.ok('Heap: ' .. heap)
  end
end

-- Start the server for real: with its input closed it loads everything, then
-- exits. A file failing to load is otherwise silent, showing up later only as
-- every goal state coming back empty.
---@param hol string
---@param dir string
local function check_startup(hol, dir)
  local result = vim
    .system({ hol, 'lsp' }, {
      cwd = dir,
      stdin = '',
      text = true,
      timeout = 30000,
    })
    :wait()
  local problems = {}
  for line in (result.stderr or ''):gmatch('[^\n]+') do
    if line:match('did not load') or line:match("Couldn't load") then
      table.insert(problems, line)
    end
  end
  if #problems > 0 then
    health.error(
      '`hol lsp` started with errors:\n' .. table.concat(problems, '\n'),
      {
        'Usually a stale build: in the HOL directory, run '
          .. '`poly < tools/smart-configure.sml`, then `bin/build`',
      }
    )
  elseif result.code ~= 0 then
    health.error(
      ('`hol lsp` exited with code %d%s'):format(
        result.code,
        result.code == 124 and ' (timed out)' or ''
      ),
      { vim.trim(result.stderr or '') }
    )
  else
    health.ok('`hol lsp` starts cleanly from ' .. dir)
  end
end

local function check_server()
  health.start('HOL')
  local hol4 = require('hol4')
  local dir = script_dir()
  local configured = hol4.opts.hol
  local chosen = dir and hol4._hol_for(dir) or configured
  local path = vim.fn.exepath(chosen)
  if path == '' then
    health.error('`' .. chosen .. '` is not executable', {
      'Build HOL, or set the `hol` option to the path of `bin/hol`',
    })
    return
  end
  health.ok(
    ('`hol`: %s%s'):format(
      path,
      chosen ~= configured and ' (last built ' .. dir .. ')' or ''
    )
  )
  check_build(path)
  check_startup(path, dir or vim.fs.dirname(vim.fs.dirname(path)))
end

local function check_neovim()
  health.start('Neovim')
  if vim.fn.has('nvim-0.12') == 1 then
    health.ok('Version ' .. tostring(vim.version()))
  else
    health.error(
      'Needs Neovim 0.12 or later, found ' .. tostring(vim.version())
    )
  end
  if vim.filetype.match { filename = 'fooScript.sml' } == 'hol4script' then
    health.ok('`*Script.sml` files are detected as `hol4script`')
  else
    health.error('`*Script.sml` files are not detected as `hol4script`', {
      "Is the plugin's `ftdetect/` on 'runtimepath'?",
    })
  end
  local syntax = vim.tbl_filter(
    function(f) return f:match('%.vim$') end,
    vim.api.nvim_get_runtime_file('syntax/hol4script.*', true)
  )
  if #syntax > 0 or require('hol4')._vim_mode_syntax() then
    health.ok('Syntax highlighting available')
  else
    health.warn('No syntax file for `hol4script`', {
      'Expected `hol4script.vim` from the Vim mode next to this plugin',
    })
  end
end

local function check_lsp()
  health.start('Language server')
  local hol4 = require('hol4')
  if not hol4.did_setup then
    health.info('`setup()` has not run: it runs when a HOL script opens')
    return
  end
  if vim.lsp.config.hol and vim.lsp.is_enabled('hol') then
    health.ok('The `hol` server is enabled')
  else
    health.error('The `hol` server is not enabled', {
      'Something has disabled it since `setup()`',
    })
  end
  local clients = vim.lsp.get_clients { name = 'hol' }
  if #clients == 0 then
    health.info('No servers running')
  else
    for _, client in ipairs(clients) do
      local files = vim.tbl_map(
        function(b)
          return vim.fn.fnamemodify(vim.api.nvim_buf_get_name(b), ':t')
        end,
        vim.tbl_keys(client.attached_buffers)
      )
      health.info(
        ('Running: %s (%s)'):format(table.concat(files, ', '), client.root_dir)
      )
    end
  end
end

local function check_picker()
  health.start('Theorem search')
  local has = {
    snacks = pcall(require, 'snacks') and rawget(_G, 'Snacks') ~= nil,
    telescope = pcall(require, 'telescope'),
    select = true,
  }
  local wanted = require('hol4').opts.picker
  if wanted and not has[wanted] then
    health.error(
      'The `picker` option is `' .. wanted .. '`, which is not installed'
    )
  elseif wanted then
    health.ok('Using ' .. wanted)
  elseif has.snacks or has.telescope then
    health.ok('Using ' .. (has.snacks and 'snacks' or 'telescope'))
  else
    health.info(
      'Using `vim.ui.select`; snacks.nvim or telescope.nvim search as you type'
    )
  end
end

function M.check()
  check_neovim()
  check_server()
  check_lsp()
  check_picker()
end

return M
