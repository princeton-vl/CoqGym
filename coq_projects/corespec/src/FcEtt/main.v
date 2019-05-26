(* Combining all the parametrized modules together
   This serves both as an entry point for the proofs (combining all results)
   and a simple sanity check. *)

Require Import FcEtt.ext_wf.
Require Import FcEtt.ext_weak.
Require Import FcEtt.ext_subst.
Require Import FcEtt.ext_invert.
Require Import FcEtt.ext_red.
Require Import FcEtt.ext_red_one.

Require Import FcEtt.fc_wf.
Require Import FcEtt.fc_weak.
Require Import FcEtt.fc_subst.
Require Import FcEtt.fc_unique.
Require Import FcEtt.fc_invert.
Require Import FcEtt.fc_get.
Require Import FcEtt.fc_dec.
Require Import FcEtt.fc_preservation.
Require Import FcEtt.fc_consist.
Require Import FcEtt.fc_head_reduction.

Require Import FcEtt.erase.
Require Import FcEtt.ext_consist.


Module ext_weak    := ext_weak ext_wf.
Module ext_subst   := ext_subst ext_weak.
Module ext_invert  := ext_invert ext_subst.
Module ext_red     := ext_red ext_invert.
Module ext_red_one := ext_red_one ext_invert.

Module fc_weak           := fc_weak fc_wf.
Module fc_subst          := fc_subst fc_wf fc_weak.
Module fc_unique         := fc_unique fc_wf fc_subst.
Module fc_invert         := fc_invert fc_wf fc_weak fc_subst.
Module fc_get            := fc_get fc_wf fc_weak fc_subst fc_unique.
Module fc_dec            := fc_dec fc_wf fc_weak fc_subst fc_unique.
Module fc_preservation   := fc_preservation fc_wf fc_weak fc_subst ext_subst.
Module fc_consist        := fc_consist fc_wf fc_weak fc_subst.
Module fc_head_reduction := fc_head_reduction ext_invert.

Module erase       := erase fc_wf fc_weak fc_subst.
Module ext_consist := ext_consist ext_invert fc_wf.
