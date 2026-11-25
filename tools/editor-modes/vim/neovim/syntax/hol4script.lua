-- The Vim mode's syntax file, one directory up; a syntax file earlier in
-- 'runtimepath' (a user's own copy) takes precedence.
if vim.b.current_syntax then return end
local here = vim.fs.dirname(debug.getinfo(1, 'S').source:sub(2))
local path = vim.fs.joinpath(here, '..', '..', 'hol4script.vim')
if vim.uv.fs_stat(path) then vim.cmd.source(path) end
