(** Coq configuration for std++ (not meant to leak to clients) *)
(* Everything here should be [Export Set], which means when this
file is *imported*, the option will only apply on the import site
but not transitively. *)

Export Set Default Proof Using "Type".
(* FIXME: cannot enable this yet as some files disable 'Default Proof Using'.
Export Set Suggest Proof Using. *)
Export Set Default Goal Selector "!".
Export Set Mangle Names.
Export Set Mangle Names Light.
(** Make these names stand out more, in case one does end up in the proof script. *)
Export Set Mangle Names Prefix "__".

(* "Fake" import to whitelist this file for the check that ensures we import
this file everywhere.
From stdpp Require Import options.
*)
