From Coq Require Import Ascii.
From Coq Require String.
From stdpp Require Export list.
From stdpp Require Import countable.
From stdpp Require Import options.

(** We define the ascii/string methods in corresponding modules, similar to what
is done for numbers. These modules should generally not be imported, e.g., use
[Ascii.is_nat] instead. *)

(** To avoid poluting the global namespace, we export only the [string] data
type (with its constructors and eliminators) and notations. *)
Export String (string(..)).
Export (notations) String.

(** Enable the string literal and append notation in [stdpp_scope], making
it possible to write string literals as "foo" instead of "foo"%string.
One could also enable the string literal notation via [Open Scope string_scope]
but that overrides various notations (e.g, [=?] on [nat]) with the version for
strings. *)
String Notation string
  String.string_of_list_byte String.list_byte_of_string : stdpp_scope.

Infix "+:+" := String.append (at level 60, right associativity) : stdpp_scope.

(** * Encoding and decoding *)
(** The [Countable] instance of [string] is particularly useful to allow strings
to be used as keys in [gmap].

The encoding of [string] to [positive] is taken from
https://github.com/xavierleroy/canonical-binary-tries/blob/v2/lib/String2pos.v.
It avoids creating auxiliary data structures such as [list bool], thereby
improving efficiency.

We first provide some [Local] helper functions and then define the [Countable]
instances for encoding/decoding in the modules [Ascii] and [String]. End-users
should always use these instances. *)
Local Definition bool_cons_pos (b : bool) (p : positive) : positive :=
  if b then p~1 else p~0.
Local Definition ascii_cons_pos (c : ascii) (p : positive) : positive :=
  match c with
  | Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
     bool_cons_pos b0 $ bool_cons_pos b1 $ bool_cons_pos b2 $
       bool_cons_pos b3 $ bool_cons_pos b4 $ bool_cons_pos b5 $
       bool_cons_pos b6 $ bool_cons_pos b7 p
  end.
Local Fixpoint string_to_pos (s : string) : positive :=
  match s with
  | EmptyString => 1
  | String c s => ascii_cons_pos c (string_to_pos s)
  end.

(* The decoder that turns [positive] into string results in 256 cases (we need
to peel off 8 times a [~0]/[~1] constructor) and a number of fall through cases.
We avoid writing these cases explicitly by generating the definition using Ltac.
The lemma [string_of_to_pos] ensures the generated definition is correct.

Alternatively, we could implement it in two steps. Convert the [positive] to
[list bool], and convert the list to [string]. This definition will be slower
since auxiliary data structures are created. *)
Local Fixpoint pos_to_string (p : positive) : string.
Proof.
  (** The argument [p] is the [positive] that we are peeling off.
  The argument [a] is the constructor [Ascii] partially applied to some number
  of Booleans (so its Coq type changes during the iteration).
  The argument [n] says how many more Booleans are needed to make this fully
  applied so that the [constr] has type ascii. *)
  let rec gen p a n :=
    lazymatch n with
    (* This character is done. Stop the ltac recursion; recursively invoke
    [pos_to_string] on the Gallina level for the remaining bits. *)
    | 0 => exact (String a (pos_to_string p))
    (* There are more bits to consume for this character, generate an
    appropriate [match] with ltac. *)
    | S ?n =>
       exact (match p with
              | 1 => EmptyString
              | p~0 => ltac:(gen p (a false) n)
              | p~1 => ltac:(gen p (a true) n)
              end%positive)
    end in
  gen p Ascii 8.
Defined.

Local Lemma pos_to_string_string_to_pos s : pos_to_string (string_to_pos s) = s.
Proof. induction s as [|[[][][][][][][][]]]; by f_equal/=. Qed.

Module Ascii.
  Global Instance eq_dec : EqDecision ascii := ascii_dec.

  Global Program Instance countable : Countable ascii := {|
    encode a := string_to_pos (String a EmptyString);
    decode p := match pos_to_string p return _ with String a _ => Some a | _ => None end
  |}.
  Next Obligation. by intros [[] [] [] [] [] [] [] []]. Qed.

  Definition is_nat (x : ascii) : option nat :=
    match x with
    | "0" => Some 0
    | "1" => Some 1
    | "2" => Some 2
    | "3" => Some 3
    | "4" => Some 4
    | "5" => Some 5
    | "6" => Some 6
    | "7" => Some 7
    | "8" => Some 8
    | "9" => Some 9
    | _ => None
    end%char.

  Definition is_space (x : ascii) : bool :=
    match x with
    | "009" | "010" | "011" | "012" | "013" | " " => true | _ => false
    end%char.
End Ascii.

Module String.
  (** Use a name that is consistent with [list]. *)
  Notation app := String.append.

  (** And obtain a proper behavior for [simpl]. *)
  Global Arguments app : simpl never.

  Global Instance eq_dec : EqDecision string.
  Proof. solve_decision. Defined.
  Global Instance app_inj s1 : Inj (=) (=) (app s1).
  Proof. intros ???. induction s1; simplify_eq/=; f_equal/=; auto. Qed.

  Global Instance inhabited : Inhabited string := populate "".

  Global Program Instance countable : Countable string := {|
    encode := string_to_pos;
    decode p := Some (pos_to_string p)
  |}.
  Solve Obligations with
    naive_solver eauto using pos_to_string_string_to_pos with f_equal.

  Fixpoint rev_app (s1 s2 : string) : string :=
    match s1 with
    | "" => s2
    | String a s1 => rev_app s1 (String a s2)
    end.
  Definition rev (s : string) : string := rev_app s "".

  (* Break a string up into lists of words, delimited by white space *)
  Fixpoint words_go (cur : option string) (s : string) : list string :=
    match s with
    | "" => option_list (rev <$> cur)
    | String a s =>
       if Ascii.is_space a
       then option_list (rev <$> cur) ++ words_go None s
       else words_go (Some (from_option (String a) (String a "") cur)) s
    end.
  Definition words : string → list string := words_go None.

  Ltac words s :=
    match type of s with
    | list string => s
    | string => eval vm_compute in (words s)
    end.
End String.
