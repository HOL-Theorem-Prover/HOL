(* Stack.sig *)

(* This module implements stacks (LIFOs), with in-place modification. *)

type 'a t;
        (* The type of stacks containing elements of type ['a]. *)

exception Empty;
        (* Raised when [pop] is applied to an empty stack. *)

val new: unit -> '_a t;
      (* Return a new stack, initially empty. *)
val push: 'a -> 'a t -> unit;
      (* [push x s] adds the element [x] at the top of stack [s]. *)
val pop: 'a t -> 'a;
      (* [pop s] removes and returns the topmost element in stack [s],
         or raises [Empty] if the stack is empty. *)
val peek: 'a t -> 'a;
      (* [pop s] returns the topmost element in stack [s],
         without removing it, or raises [Empty] if the stack is empty. *)
val update: 'a -> 'a t -> unit;
      (* [update x s] replaces the top element of stack [s] with [x]. *)
val null: 'a t -> bool;
      (* [null s] returns true iff stack [s] is empty. *)
val clear : 'a t -> unit;
      (* Discard all elements from a stack. *)
