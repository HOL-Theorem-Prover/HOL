signature Htmlsigs = sig
val sigsToHtml    : string -> string -> string list -> string -> string
                    -> (string * string) list -> string * string -> unit
val printHTMLBase : string -> string -> string ->
                    (Database.entry -> bool) -> string ->
                    string * string -> unit
val listDir : string -> string list

(* URL base for per-entry docfile hyperlinks emitted into the generated
   htmlsigs/<struct>.html pages.  When empty (the default), the legacy
   `file://<abspath>` URL is emitted -- usable only on the local
   filesystem.  When set to a relative prefix (e.g.
   "../../../Manual/book/Reference/" for the mdbook Reference pages, or
   "../../Docfiles/HTML/" for the fallback per-entry HTML pipeline),
   per-entry links are emitted as `<prefix><entry-name>.html`.  Set by
   makebase.sml from its --entry-url-base CLI flag, which build_help in
   tools/build/buildutils.sml supplies based on which docfile-HTML
   pathway the current build is using. *)
val entry_url_base : string ref
end
