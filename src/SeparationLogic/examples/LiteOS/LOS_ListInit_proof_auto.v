Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import LOS_ListInit_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LiteOS.lib.glob_vars_and_defs.
Require Import SimpleC.EE.LiteOS.lib.Los_Verify_State_def.
Require Import SimpleC.EE.LiteOS.lib.sortlink.
Require Import SimpleC.EE.LiteOS.lib.dll.
Require Import SimpleC.EE.LiteOS.lib.tick_backup.
Local Open Scope sac.

