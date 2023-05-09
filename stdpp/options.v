(** Coq configuration for std++ (not meant to leak to clients) *)
(* Everything here should be [Export Set], which means when this
file is *imported*, the option will only apply on the import site
but not transitively. *)

(** Allow async proof-checking of sections. *)
Export Set Default Proof Using "Type".
(* FIXME: cannot enable this yet as some files disable 'Default Proof Using'.
Export Set Suggest Proof Using. *)

(** Enforces that every tactic is executed with a single focused goal, meaning
that bullets and curly braces must be used to structure the proof. *)
Export Set Default Goal Selector "!".

(* "Fake" import to whitelist this file for the check that ensures we import
this file everywhere.
From stdpp Require Import options.
*)
