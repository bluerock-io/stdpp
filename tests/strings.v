From stdpp Require Import strings.
From Coq Require Ascii.

(** Check that the string notation works without [%string]. *)
Check "foo".

(** And also with [%string], which should not be pretty printed) *)
Check "foo"%string.

(** Check that importing [strings] does not override notations for [nat] and
[list]. *)
Check (10 =? 10).
Check ([10] ++ [12]).

Check ("foo" =? "bar")%string.

(** Check that append on strings is pretty printed correctly, and not as
[(_ ++ _)%string]. *)
Check ("foo" +:+ "bar").

(** Should print as [String.app] *)
Check String.app.
