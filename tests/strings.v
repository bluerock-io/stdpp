From stdpp Require Import strings.

(** Check that the string notation works without [%string]. *)
Check "foo".

(** Check that importing [strings] does not override notations for [nat] and
[list]. *)
Check (10 =? 10).
Check ([10] ++ [12]).

(** Check that append on strings is pretty printed correctly, and not as
[(_ ++ _)%string]. *)
Check ("foo" +:+ "bar").
