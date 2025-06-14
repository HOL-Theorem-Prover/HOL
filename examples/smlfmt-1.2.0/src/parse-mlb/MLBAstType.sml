(** Copyright (c) 2021 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure MLBAstType =
struct

  datatype basexp =

  (** basid *)
    Ident of MLBToken.t

  (** let basdec in basexp end *)
  | LetInEnd of
      { lett: MLBToken.t
      , basdec: basdec
      , inn: MLBToken.t
      , basexp: basexp
      , endd: MLBToken.t
      }

  (** bas basdec end *)
  | BasEnd of {bas: MLBToken.t, basdec: basdec, endd: MLBToken.t}


  and basdec =
    DecEmpty

  (** basdec [;] basdec *)
  | DecMultiple of {elems: basdec Seq.t, delims: MLBToken.t option Seq.t}

  (** path/to/file.mlb *)
  | DecPathMLB of {path: FilePath.t, token: MLBToken.t}

  (** path/to/file.{sml,sig,fun} *)
  | DecPathSML of {path: FilePath.t, token: MLBToken.t}

  (** basis basid = basexp [and ...] *)
  | DecBasis of
      { basis: MLBToken.t
      , elems: {basid: MLBToken.t, eq: MLBToken.t, basexp: basexp} Seq.t
      (** 'and' delims *)
      , delims: MLBToken.t Seq.t
      }

  (** local basdec in basdec end *)
  | DecLocalInEnd of
      { locall: MLBToken.t
      , basdec1: basdec
      , inn: MLBToken.t
      , basdec2: basdec
      , endd: MLBToken.t
      }

  (** open basid ... basid *)
  | DecOpen of {openn: MLBToken.t, elems: MLBToken.t Seq.t}

  (** structure strid [= strid] [and ...] *)
  | DecStructure of
      { structuree: MLBToken.t
      , elems:
          { strid: MLBToken.t
          , eqstrid: {eq: MLBToken.t, strid: MLBToken.t} option
          } Seq.t
      (** 'and' delimiters *)
      , delims: MLBToken.t Seq.t
      }

  (** signature sigid [= sigid] [and ...] *)
  | DecSignature of
      { signaturee: MLBToken.t
      , elems:
          { sigid: MLBToken.t
          , eqsigid: {eq: MLBToken.t, sigid: MLBToken.t} option
          } Seq.t
      (** 'and' delimiters *)
      , delims: MLBToken.t Seq.t
      }

  (** functor funid [= funid] [and ...] *)
  | DecFunctor of
      { functorr: MLBToken.t
      , elems:
          { funid: MLBToken.t
          , eqfunid: {eq: MLBToken.t, funid: MLBToken.t} option
          } Seq.t
      (** 'and' delimiters *)
      , delims: MLBToken.t Seq.t
      }

  | DecAnn of
      { ann: MLBToken.t
      , annotations: MLBToken.t Seq.t
      , inn: MLBToken.t
      , basdec: basdec
      , endd: MLBToken.t
      }

  (** MLton specific *)
  | DecUnderscorePrim of MLBToken.t


  datatype ast = Ast of basdec
  type t = ast

end
