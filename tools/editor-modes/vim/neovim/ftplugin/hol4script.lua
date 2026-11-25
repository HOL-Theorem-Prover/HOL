vim.bo.commentstring = '(* %s *)'
-- A line starting `>>` continues a proof; it isn't a quoted-text leader
vim.opt_local.comments:remove('n:>')

vim.b.undo_ftplugin = (vim.b.undo_ftplugin or '')
  .. '\n setlocal commentstring< comments<'
