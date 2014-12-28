signature CoreKernel = sig
  structure Tag  : FinalTag
  structure Type : sig
    include FinalType
    val to_kt : hol_type -> KernelTypes.hol_type
    end

  structure Term : sig
    include FinalTerm        where type hol_type = Type.hol_type
    val to_kt : term -> KernelTypes.term
    end

  structure Thm  : sig
    include FinalThm         where type hol_type = Type.hol_type
			       and type term     = Term.term
			       and type tag      = Tag.tag
    val to_kt : thm -> KernelTypes.thm
    end

  structure Net : Net               where type term = Term.term

end;
