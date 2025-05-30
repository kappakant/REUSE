(* automatically generated -- do not edit manually *)
theory PetersonLemmas imports Constant Zenon begin
ML_command {* writeln ("*** TLAPS PARSED\n"); *}
consts
  "isReal" :: c
  "isa_slas_a" :: "[c,c] => c"
  "isa_bksl_diva" :: "[c,c] => c"
  "isa_perc_a" :: "[c,c] => c"
  "isa_peri_peri_a" :: "[c,c] => c"
  "isInfinity" :: c
  "isa_lbrk_rbrk_a" :: "[c] => c"
  "isa_less_more_a" :: "[c] => c"

lemma ob'6:
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_VARIABLEunde_turnunde_a a_VARIABLEunde_turnunde_a'
fixes a_VARIABLEunde_processStateunde_a a_VARIABLEunde_processStateunde_a'
fixes a_VARIABLEunde_flagunde_a a_VARIABLEunde_flagunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_ProcessBeginWaiting_ suppressed *)
(* usable definition ACTION_ProcessEnterCritical_ suppressed *)
(* usable definition ACTION_ProcessExitCritical_ suppressed *)
(* usable definition ACTION_Process0_ suppressed *)
(* usable definition ACTION_Process1_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition TEMPORAL_SpecWithFairness_ suppressed *)
(* usable definition STATE_MutualExclusion_ suppressed *)
(* usable definition TEMPORAL_WillEventuallyEnterCritical_ suppressed *)
(* usable definition STATE_CanOnlyBeCriticalIfTurn_ suppressed *)
(* usable definition STATE_I_ suppressed *)
assumes v'24: "(((((a_VARIABLEunde_turnunde_a) \<in> ({((0)), ((Succ[0]))}))) & (((a_VARIABLEunde_flagunde_a) \<in> ([({((0)), ((Succ[0]))}) \<rightarrow> ({(TRUE), (FALSE)})]))) & (((a_VARIABLEunde_processStateunde_a) \<in> ([({((0)), ((Succ[0]))}) \<rightarrow> ({(''idle''), (''sentRequest''), (''waiting''), (''critical'')})])))) & (a_STATEunde_Iunde_a) & (a_STATEunde_MutualExclusionunde_a))"
assumes v'25: "(a_ACTIONunde_Nextunde_a)"
assumes v'26: "(((fapply ((a_VARIABLEunde_processStateunde_a), ((0)))) = (''idle'')))"
assumes v'27: "((((a_VARIABLEunde_flagunde_hash_primea :: c)) = ([(a_VARIABLEunde_flagunde_a) EXCEPT ![((0))] = (TRUE)])))"
assumes v'28: "((((a_VARIABLEunde_processStateunde_hash_primea :: c)) = ([(a_VARIABLEunde_processStateunde_a) EXCEPT ![((0))] = (''sentRequest'')])))"
assumes v'29: "((((a_VARIABLEunde_turnunde_hash_primea :: c)) = (a_VARIABLEunde_turnunde_a)))"
assumes v'38: "((((a_VARIABLEunde_turnunde_a) \<in> ({((0)), ((Succ[0]))}))) & (((a_VARIABLEunde_flagunde_a) \<in> ([({((0)), ((Succ[0]))}) \<rightarrow> ({(TRUE), (FALSE)})]))) & (((a_VARIABLEunde_processStateunde_a) \<in> ([({((0)), ((Succ[0]))}) \<rightarrow> ({(''idle''), (''sentRequest''), (''waiting''), (''critical'')})]))))"
assumes v'39: "((((a_VARIABLEunde_turnunde_hash_primea :: c)) \<in> ({((0)), ((Succ[0]))})))"
assumes v'40: "(\<forall> a_CONSTANTunde_punde_a \<in> ({((0)), ((Succ[0]))}) : (((fapply (((a_VARIABLEunde_flagunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<in> ({(TRUE), (FALSE)}))))"
assumes v'41: "((((a_VARIABLEunde_processStateunde_hash_primea :: c)) \<in> ([({((0)), ((Succ[0]))}) \<rightarrow> ({(''idle''), (''sentRequest''), (''waiting''), (''critical'')})])))"
shows "(((((a_VARIABLEunde_turnunde_hash_primea :: c)) \<in> ({((0)), ((Succ[0]))}))) & ((((a_VARIABLEunde_flagunde_hash_primea :: c)) \<in> ([({((0)), ((Succ[0]))}) \<rightarrow> ({(TRUE), (FALSE)})]))) & ((((a_VARIABLEunde_processStateunde_hash_primea :: c)) \<in> ([({((0)), ((Succ[0]))}) \<rightarrow> ({(''idle''), (''sentRequest''), (''waiting''), (''critical'')})]))))"(is "PROP ?ob'6")
proof -
ML_command {* writeln "*** TLAPS ENTER 6"; *}
show "PROP ?ob'6"

(* BEGIN ZENON INPUT
;; file=.tlacache/PetersonLemmas.tlaps/tlapm_cc9688.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/PetersonLemmas.tlaps/tlapm_cc9688.znn.out
;; obligation #6
$hyp "v'24" (/\ (/\ (TLA.in a_VARIABLEunde_turnunde_a
(TLA.set 0 (TLA.fapply TLA.Succ 0))) (TLA.in a_VARIABLEunde_flagunde_a
(TLA.FuncSet (TLA.set 0 (TLA.fapply TLA.Succ 0)) (TLA.set T. F.)))
(TLA.in a_VARIABLEunde_processStateunde_a
(TLA.FuncSet (TLA.set 0 (TLA.fapply TLA.Succ 0)) (TLA.set "idle" "sentRequest" "waiting" "critical"))))
a_STATEunde_Iunde_a
a_STATEunde_MutualExclusionunde_a)
$hyp "v'25" a_ACTIONunde_Nextunde_a
$hyp "v'26" (= (TLA.fapply a_VARIABLEunde_processStateunde_a 0)
"idle")
$hyp "v'27" (= a_VARIABLEunde_flagunde_hash_primea
(TLA.except a_VARIABLEunde_flagunde_a 0 T.))
$hyp "v'28" (= a_VARIABLEunde_processStateunde_hash_primea
(TLA.except a_VARIABLEunde_processStateunde_a 0 "sentRequest"))
$hyp "v'29" (= a_VARIABLEunde_turnunde_hash_primea
a_VARIABLEunde_turnunde_a)
$hyp "v'38" (/\ (TLA.in a_VARIABLEunde_turnunde_a
(TLA.set 0 (TLA.fapply TLA.Succ 0))) (TLA.in a_VARIABLEunde_flagunde_a
(TLA.FuncSet (TLA.set 0 (TLA.fapply TLA.Succ 0)) (TLA.set T. F.)))
(TLA.in a_VARIABLEunde_processStateunde_a
(TLA.FuncSet (TLA.set 0 (TLA.fapply TLA.Succ 0)) (TLA.set "idle" "sentRequest" "waiting" "critical"))))
$hyp "v'39" (TLA.in a_VARIABLEunde_turnunde_hash_primea
(TLA.set 0 (TLA.fapply TLA.Succ 0)))
$hyp "v'40" (TLA.bAll (TLA.set 0 (TLA.fapply TLA.Succ 0)) ((a_CONSTANTunde_punde_a) (TLA.in (TLA.fapply a_VARIABLEunde_flagunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.set T. F.))))
$hyp "v'41" (TLA.in a_VARIABLEunde_processStateunde_hash_primea
(TLA.FuncSet (TLA.set 0 (TLA.fapply TLA.Succ 0)) (TLA.set "idle" "sentRequest" "waiting" "critical")))
$goal (/\ (TLA.in a_VARIABLEunde_turnunde_hash_primea
(TLA.set 0 (TLA.fapply TLA.Succ 0)))
(TLA.in a_VARIABLEunde_flagunde_hash_primea
(TLA.FuncSet (TLA.set 0 (TLA.fapply TLA.Succ 0)) (TLA.set T. F.)))
(TLA.in a_VARIABLEunde_processStateunde_hash_primea
(TLA.FuncSet (TLA.set 0 (TLA.fapply TLA.Succ 0)) (TLA.set "idle" "sentRequest" "waiting" "critical"))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(((a_VARIABLEunde_turnunde_a \\in {0, 1})&((a_VARIABLEunde_flagunde_a \\in FuncSet({0, 1}, {TRUE, FALSE}))&(a_VARIABLEunde_processStateunde_a \\in FuncSet({0, 1}, {''idle'', ''sentRequest'', ''waiting'', ''critical''}))))&(a_STATEunde_Iunde_a&a_STATEunde_MutualExclusionunde_a))" (is "?z_hg&?z_hbf")
 using v'24 by blast
 have z_Hh:"(a_VARIABLEunde_turnunde_hash_primea \\in {0, 1})" (is "?z_hh")
 using v'39 by blast
 have z_Hd:"(a_VARIABLEunde_flagunde_hash_primea=except(a_VARIABLEunde_flagunde_a, 0, TRUE))" (is "_=?z_hbk")
 using v'27 by blast
 have z_Hj:"(a_VARIABLEunde_processStateunde_hash_primea \\in FuncSet({0, 1}, {''idle'', ''sentRequest'', ''waiting'', ''critical''}))" (is "?z_hj")
 using v'41 by blast
 assume z_Hk:"(~(?z_hh&((a_VARIABLEunde_flagunde_hash_primea \\in FuncSet({0, 1}, {TRUE, FALSE}))&?z_hj)))" (is "~(_&?z_hbn)")
 have z_Hg: "?z_hg" (is "?z_hl&?z_hq")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hq: "?z_hq" (is "?z_hr&?z_hx")
 by (rule zenon_and_1 [OF z_Hg])
 have z_Hr: "?z_hr"
 by (rule zenon_and_0 [OF z_Hq])
 show FALSE
 proof (rule zenon_notand [OF z_Hk])
  assume z_Hbp:"(~?z_hh)"
  show FALSE
  by (rule notE [OF z_Hbp z_Hh])
 next
  assume z_Hbq:"(~?z_hbn)" (is "~(?z_hbo&_)")
  show FALSE
  proof (rule zenon_notand [OF z_Hbq])
   assume z_Hbr:"(~?z_hbo)"
   have z_Hbs: "(~(?z_hbk \\in FuncSet({0, 1}, {TRUE, FALSE})))" (is "~?z_hbt")
   by (rule subst [where P="(\<lambda>zenon_Vda. (~(zenon_Vda \\in FuncSet({0, 1}, {TRUE, FALSE}))))", OF z_Hd z_Hbr])
   show FALSE
   proof (rule zenon_except_notin_funcset [of "a_VARIABLEunde_flagunde_a" "0" "TRUE" "{0, 1}" "{TRUE, FALSE}", OF z_Hbs])
    assume z_Hby:"(~?z_hr)"
    show FALSE
    by (rule notE [OF z_Hby z_Hr])
   next
    assume z_Hbz:"(~(TRUE \\in {TRUE, FALSE}))" (is "~?z_hca")
    have z_Hcb: "(TRUE~=TRUE)" (is "?z_hv~=_")
    by (rule zenon_notin_addElt_0 [of "?z_hv" "?z_hv" "{FALSE}", OF z_Hbz])
    show FALSE
    by (rule zenon_noteq [OF z_Hcb])
   qed
  next
   assume z_Hcd:"(~?z_hj)"
   show FALSE
   by (rule notE [OF z_Hcd z_Hj])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 6"; *} qed
end
