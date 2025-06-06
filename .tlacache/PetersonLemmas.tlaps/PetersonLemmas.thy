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

lemma ob'13:
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_VARIABLEunde_turnunde_a a_VARIABLEunde_turnunde_a'
fixes a_VARIABLEunde_processStateunde_a a_VARIABLEunde_processStateunde_a'
fixes a_VARIABLEunde_flagunde_a a_VARIABLEunde_flagunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_ProcessRequestFlag_ suppressed *)
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
(* usable definition STATE_critReqs_ suppressed *)
(* usable definition STATE_requestReqs_ suppressed *)
(* usable definition STATE_waitReqs_ suppressed *)
(* usable definition STATE_I_ suppressed *)
(* usable definition TEMPORAL_MutExSpec_ suppressed *)
(* usable definition TEMPORAL_TestSpec_ suppressed *)
(* usable definition STATE_InvImpMutEx_ suppressed *)
assumes v'32: "((a_STATEunde_TypeOKunde_a) & (a_STATEunde_Iunde_a) & (a_STATEunde_MutualExclusionunde_a))"
assumes v'33: "((a_ACTIONunde_ProcessRequestFlagunde_a (((0)))))"
assumes v'45: "(\<forall> a_CONSTANTunde_punde_a \<in> ({((0)), ((Succ[0]))}) : (((fapply ((a_VARIABLEunde_flagunde_a), (a_CONSTANTunde_punde_a))) \<in> ({(TRUE), (FALSE)}))))"
assumes v'46: "((((a_VARIABLEunde_flagunde_hash_primea :: c)) = ([(a_VARIABLEunde_flagunde_a) EXCEPT ![((0))] = (TRUE)])))"
assumes v'47: "((((a_VARIABLEunde_flagunde_hash_primea :: c)) \<in> ([({((0)), ((Succ[0]))}) \<rightarrow> ({(TRUE), (FALSE)})])))"
shows "(\<forall> a_CONSTANTunde_punde_a \<in> ({((0)), ((Succ[0]))}) : (((fapply (((a_VARIABLEunde_flagunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<in> ({(TRUE), (FALSE)}))))"(is "PROP ?ob'13")
proof -
ML_command {* writeln "*** TLAPS ENTER 13"; *}
show "PROP ?ob'13"

(* BEGIN ZENON INPUT
;; file=.tlacache/PetersonLemmas.tlaps/tlapm_46129d.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/PetersonLemmas.tlaps/tlapm_46129d.znn.out
;; obligation #13
$hyp "v'32" (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Iunde_a
a_STATEunde_MutualExclusionunde_a)
$hyp "v'33" (a_ACTIONunde_ProcessRequestFlagunde_a 0)
$hyp "v'45" (TLA.bAll (TLA.set 0 (TLA.fapply TLA.Succ 0)) ((a_CONSTANTunde_punde_a) (TLA.in (TLA.fapply a_VARIABLEunde_flagunde_a a_CONSTANTunde_punde_a)
(TLA.set T. F.))))
$hyp "v'46" (= a_VARIABLEunde_flagunde_hash_primea
(TLA.except a_VARIABLEunde_flagunde_a 0 T.))
$hyp "v'47" (TLA.in a_VARIABLEunde_flagunde_hash_primea
(TLA.FuncSet (TLA.set 0 (TLA.fapply TLA.Succ 0)) (TLA.set T. F.)))
$goal (TLA.bAll (TLA.set 0 (TLA.fapply TLA.Succ 0)) ((a_CONSTANTunde_punde_a) (TLA.in (TLA.fapply a_VARIABLEunde_flagunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.set T. F.))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hd:"(a_VARIABLEunde_flagunde_hash_primea=except(a_VARIABLEunde_flagunde_a, 0, TRUE))" (is "_=?z_hh")
 using v'46 by blast
 have z_Hc:"bAll({0, 1}, (\<lambda>a_CONSTANTunde_punde_a. ((a_VARIABLEunde_flagunde_a[a_CONSTANTunde_punde_a]) \\in {TRUE, FALSE})))" (is "?z_hc")
 using v'45 by blast
 have z_He:"(a_VARIABLEunde_flagunde_hash_primea \\in FuncSet({0, 1}, {TRUE, FALSE}))" (is "?z_he")
 using v'47 by blast
 have zenon_L1_: "(~(1 \\in {0, 1})) ==> FALSE" (is "?z_hu ==> FALSE")
 proof -
  assume z_Hu:"?z_hu" (is "~?z_hv")
  have z_Hw: "(~(1 \\in {1}))" (is "~?z_hx")
  by (rule zenon_notin_addElt_1 [of "1" "0" "{1}", OF z_Hu])
  have z_Hz: "(1~=1)" (is "?z_hm~=_")
  by (rule zenon_notin_addElt_0 [of "?z_hm" "?z_hm" "{}", OF z_Hw])
  show FALSE
  by (rule zenon_noteq [OF z_Hz])
 qed
 have zenon_L2_: "(~(TRUE \\in {TRUE, FALSE})) ==> FALSE" (is "?z_hbb ==> FALSE")
 proof -
  assume z_Hbb:"?z_hbb" (is "~?z_hbc")
  have z_Hbd: "(TRUE~=TRUE)" (is "?z_hk~=_")
  by (rule zenon_notin_addElt_0 [of "?z_hk" "?z_hk" "{FALSE}", OF z_Hbb])
  show FALSE
  by (rule zenon_noteq [OF z_Hbd])
 qed
 have zenon_L3_: "(DOMAIN(a_VARIABLEunde_flagunde_a)={0, 1}) ==> (~((CHOOSE x:(~((x \\in {0, 1})=>((a_VARIABLEunde_flagunde_hash_primea[x]) \\in {TRUE, FALSE})))) \\in DOMAIN(a_VARIABLEunde_flagunde_a))) ==> ((CHOOSE x:(~((x \\in {0, 1})=>((a_VARIABLEunde_flagunde_hash_primea[x]) \\in {TRUE, FALSE})))) \\in {0, 1}) ==> FALSE" (is "?z_hbf ==> ?z_hbh ==> ?z_hbq ==> FALSE")
 proof -
  assume z_Hbf:"?z_hbf" (is "?z_hbg=?z_hl")
  assume z_Hbh:"?z_hbh" (is "~?z_hbi")
  assume z_Hbq:"?z_hbq"
  have z_Hbr: "(~?z_hbq)"
  by (rule subst [where P="(\<lambda>zenon_Vob. (~((CHOOSE x:(~((x \\in ?z_hl)=>((a_VARIABLEunde_flagunde_hash_primea[x]) \\in {TRUE, FALSE})))) \\in zenon_Vob)))", OF z_Hbf z_Hbh])
  show FALSE
  by (rule notE [OF z_Hbr z_Hbq])
 qed
 have zenon_L4_: "((a_VARIABLEunde_flagunde_a[1])~=(a_VARIABLEunde_flagunde_a[(CHOOSE x:(~((x \\in {0, 1})=>((a_VARIABLEunde_flagunde_hash_primea[x]) \\in {TRUE, FALSE}))))])) ==> ((CHOOSE x:(~((x \\in {0, 1})=>((a_VARIABLEunde_flagunde_hash_primea[x]) \\in {TRUE, FALSE}))))=1) ==> FALSE" (is "?z_hbw ==> ?z_hbz ==> FALSE")
 proof -
  assume z_Hbw:"?z_hbw" (is "?z_hbx~=?z_hby")
  assume z_Hbz:"?z_hbz" (is "?z_hbj=?z_hm")
  show FALSE
  proof (rule zenon_noteq [of "?z_hby"])
   have z_Hca: "(?z_hm=?z_hbj)"
   by (rule sym [OF z_Hbz])
   have z_Hcb: "(?z_hby~=?z_hby)"
   by (rule subst [where P="(\<lambda>zenon_Vpb. ((a_VARIABLEunde_flagunde_a[zenon_Vpb])~=?z_hby))", OF z_Hca], fact z_Hbw)
   thus "(?z_hby~=?z_hby)" .
  qed
 qed
 assume z_Hf:"(~bAll({0, 1}, (\<lambda>a_CONSTANTunde_punde_a. ((a_VARIABLEunde_flagunde_hash_primea[a_CONSTANTunde_punde_a]) \\in {TRUE, FALSE}))))" (is "~?z_hcg")
 have z_Hck_z_Hc: "(\\A x:((x \\in {0, 1})=>((a_VARIABLEunde_flagunde_a[x]) \\in {TRUE, FALSE}))) == ?z_hc" (is "?z_hck == _")
 by (unfold bAll_def)
 have z_Hck: "?z_hck" (is "\\A x : ?z_hco(x)")
 by (unfold z_Hck_z_Hc, fact z_Hc)
 have z_Hcp_z_Hf: "(~(\\A x:((x \\in {0, 1})=>((a_VARIABLEunde_flagunde_hash_primea[x]) \\in {TRUE, FALSE})))) == (~?z_hcg)" (is "?z_hcp == ?z_hf")
 by (unfold bAll_def)
 have z_Hcp: "?z_hcp" (is "~(\\A x : ?z_hcr(x))")
 by (unfold z_Hcp_z_Hf, fact z_Hf)
 have z_Hcs: "(\\E x:(~((x \\in {0, 1})=>((a_VARIABLEunde_flagunde_hash_primea[x]) \\in {TRUE, FALSE}))))" (is "\\E x : ?z_hct(x)")
 by (rule zenon_notallex_0 [of "?z_hcr", OF z_Hcp])
 have z_Hcu: "?z_hct((CHOOSE x:(~((x \\in {0, 1})=>((a_VARIABLEunde_flagunde_hash_primea[x]) \\in {TRUE, FALSE})))))" (is "~(?z_hbq=>?z_hcv)")
 by (rule zenon_ex_choose_0 [of "?z_hct", OF z_Hcs])
 have z_Hbq: "?z_hbq"
 by (rule zenon_notimply_0 [OF z_Hcu])
 have z_Hcw: "(~?z_hcv)"
 by (rule zenon_notimply_1 [OF z_Hcu])
 show FALSE
 proof (rule zenon_in_addElt [of "(CHOOSE x:(~((x \\in {0, 1})=>((a_VARIABLEunde_flagunde_hash_primea[x]) \\in {TRUE, FALSE}))))" "0" "{1}", OF z_Hbq])
  assume z_Hcx:"((CHOOSE x:(~((x \\in {0, 1})=>((a_VARIABLEunde_flagunde_hash_primea[x]) \\in {TRUE, FALSE}))))=0)" (is "?z_hbj=_")
  have z_Hcy: "(~((?z_hh[?z_hbj]) \\in {TRUE, FALSE}))" (is "~?z_hcz")
  by (rule subst [where P="(\<lambda>zenon_Vt. (~((zenon_Vt[?z_hbj]) \\in {TRUE, FALSE})))", OF z_Hd z_Hcw])
  have z_Hdg: "?z_hco(1)" (is "?z_hv=>?z_hdh")
  by (rule zenon_all_0 [of "?z_hco" "1", OF z_Hck])
  show FALSE
  proof (rule zenon_imply [OF z_Hdg])
   assume z_Hu:"(~?z_hv)"
   show FALSE
   by (rule zenon_L1_ [OF z_Hu])
  next
   assume z_Hdh:"?z_hdh"
   have z_Hdi: "(?z_hh \\in FuncSet({0, 1}, {TRUE, FALSE}))" (is "?z_hdi")
   by (rule subst [where P="(\<lambda>zenon_Vg. (zenon_Vg \\in FuncSet({0, 1}, {TRUE, FALSE})))", OF z_Hd z_He])
   have z_Hdm: "(DOMAIN(?z_hh)={0, 1})" (is "?z_hdn=?z_hl")
   by (rule zenon_in_funcset_1 [of "?z_hh" "?z_hl" "{TRUE, FALSE}", OF z_Hdi])
   have z_Hbf: "(DOMAIN(a_VARIABLEunde_flagunde_a)=?z_hl)" (is "?z_hbg=_")
   by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vta. (zenon_Vta=?z_hl))" "a_VARIABLEunde_flagunde_a" "0" "TRUE", OF z_Hdm])
   show FALSE
   proof (rule notE [OF z_Hcw])
    have z_Hdr: "((a_VARIABLEunde_flagunde_a[1])=(a_VARIABLEunde_flagunde_hash_primea[?z_hbj]))" (is "?z_hbx=?z_hds")
    proof (rule zenon_nnpp [of "(?z_hbx=?z_hds)"])
     assume z_Hdt:"(?z_hbx~=?z_hds)"
     have z_Hdu: "(?z_hbx~=(?z_hh[?z_hbj]))" (is "_~=?z_hda")
     by (rule subst [where P="(\<lambda>zenon_Vib. (?z_hbx~=(zenon_Vib[?z_hbj])))", OF z_Hd z_Hdt])
     show FALSE
     proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vib. (?z_hbx~=zenon_Vib))" "a_VARIABLEunde_flagunde_a" "0" "TRUE" "?z_hbj", OF z_Hdu])
      assume z_Hbi:"(?z_hbj \\in ?z_hbg)" (is "?z_hbi")
      assume z_Heb:"(0=?z_hbj)"
      assume z_Hec:"(?z_hbx~=TRUE)" (is "_~=?z_hk")
      show FALSE
      proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vt. (~(zenon_Vt \\in {?z_hk, FALSE})))" "a_VARIABLEunde_flagunde_a" "0" "?z_hk" "?z_hbj", OF z_Hcy])
       assume z_Hbi:"?z_hbi"
       assume z_Heb:"(0=?z_hbj)"
       assume z_Hbb:"(~(?z_hk \\in {?z_hk, FALSE}))" (is "~?z_hbc")
       show FALSE
       by (rule zenon_L2_ [OF z_Hbb])
      next
       assume z_Hbi:"?z_hbi"
       assume z_Heg:"(0~=?z_hbj)"
       assume z_Heh:"(~((a_VARIABLEunde_flagunde_a[?z_hbj]) \\in {?z_hk, FALSE}))" (is "~?z_hei")
       show FALSE
       by (rule zenon_eqsym [OF z_Hcx z_Heg])
      next
       assume z_Hbh:"(~?z_hbi)"
       show FALSE
       by (rule notE [OF z_Hbh z_Hbi])
      qed
     next
      assume z_Hbi:"(?z_hbj \\in ?z_hbg)" (is "?z_hbi")
      assume z_Heg:"(0~=?z_hbj)"
      assume z_Hbw:"(?z_hbx~=(a_VARIABLEunde_flagunde_a[?z_hbj]))" (is "_~=?z_hby")
      show FALSE
      by (rule zenon_eqsym [OF z_Hcx z_Heg])
     next
      assume z_Hbh:"(~(?z_hbj \\in ?z_hbg))" (is "~?z_hbi")
      show FALSE
      by (rule zenon_L3_ [OF z_Hbf z_Hbh z_Hbq])
     qed
    qed
    have z_Hcv: "?z_hcv"
    by (rule subst [where P="(\<lambda>zenon_Vha. (zenon_Vha \\in {TRUE, FALSE}))", OF z_Hdr], fact z_Hdh)
    thus "?z_hcv" .
   qed
  qed
 next
  assume z_Hem:"((CHOOSE x:(~((x \\in {0, 1})=>((a_VARIABLEunde_flagunde_hash_primea[x]) \\in {TRUE, FALSE})))) \\in {1})" (is "?z_hem")
  show FALSE
  proof (rule zenon_in_addElt [of "(CHOOSE x:(~((x \\in {0, 1})=>((a_VARIABLEunde_flagunde_hash_primea[x]) \\in {TRUE, FALSE}))))" "1" "{}", OF z_Hem])
   assume z_Hbz:"((CHOOSE x:(~((x \\in {0, 1})=>((a_VARIABLEunde_flagunde_hash_primea[x]) \\in {TRUE, FALSE}))))=1)" (is "?z_hbj=?z_hm")
   have z_Hcy: "(~((?z_hh[?z_hbj]) \\in {TRUE, FALSE}))" (is "~?z_hcz")
   by (rule subst [where P="(\<lambda>zenon_Vt. (~((zenon_Vt[?z_hbj]) \\in {TRUE, FALSE})))", OF z_Hd z_Hcw])
   have z_Hdg: "?z_hco(?z_hm)" (is "?z_hv=>?z_hdh")
   by (rule zenon_all_0 [of "?z_hco" "?z_hm", OF z_Hck])
   show FALSE
   proof (rule zenon_imply [OF z_Hdg])
    assume z_Hu:"(~?z_hv)"
    show FALSE
    by (rule zenon_L1_ [OF z_Hu])
   next
    assume z_Hdh:"?z_hdh"
    have z_Hdi: "(?z_hh \\in FuncSet({0, ?z_hm}, {TRUE, FALSE}))" (is "?z_hdi")
    by (rule subst [where P="(\<lambda>zenon_Vg. (zenon_Vg \\in FuncSet({0, ?z_hm}, {TRUE, FALSE})))", OF z_Hd z_He])
    have z_Hdm: "(DOMAIN(?z_hh)={0, ?z_hm})" (is "?z_hdn=?z_hl")
    by (rule zenon_in_funcset_1 [of "?z_hh" "?z_hl" "{TRUE, FALSE}", OF z_Hdi])
    have z_Hbf: "(DOMAIN(a_VARIABLEunde_flagunde_a)=?z_hl)" (is "?z_hbg=_")
    by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vta. (zenon_Vta=?z_hl))" "a_VARIABLEunde_flagunde_a" "0" "TRUE", OF z_Hdm])
    show FALSE
    proof (rule notE [OF z_Hcw])
     have z_Hdr: "((a_VARIABLEunde_flagunde_a[?z_hm])=(a_VARIABLEunde_flagunde_hash_primea[?z_hbj]))" (is "?z_hbx=?z_hds")
     proof (rule zenon_nnpp [of "(?z_hbx=?z_hds)"])
      assume z_Hdt:"(?z_hbx~=?z_hds)"
      have z_Hdu: "(?z_hbx~=(?z_hh[?z_hbj]))" (is "_~=?z_hda")
      by (rule subst [where P="(\<lambda>zenon_Vib. (?z_hbx~=(zenon_Vib[?z_hbj])))", OF z_Hd z_Hdt])
      show FALSE
      proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vib. (?z_hbx~=zenon_Vib))" "a_VARIABLEunde_flagunde_a" "0" "TRUE" "?z_hbj", OF z_Hdu])
       assume z_Hbi:"(?z_hbj \\in ?z_hbg)" (is "?z_hbi")
       assume z_Heb:"(0=?z_hbj)"
       assume z_Hec:"(?z_hbx~=TRUE)" (is "_~=?z_hk")
       show FALSE
       proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vt. (~(zenon_Vt \\in {?z_hk, FALSE})))" "a_VARIABLEunde_flagunde_a" "0" "?z_hk" "?z_hbj", OF z_Hcy])
        assume z_Hbi:"?z_hbi"
        assume z_Heb:"(0=?z_hbj)"
        assume z_Hbb:"(~(?z_hk \\in {?z_hk, FALSE}))" (is "~?z_hbc")
        show FALSE
        by (rule zenon_L2_ [OF z_Hbb])
       next
        assume z_Hbi:"?z_hbi"
        assume z_Heg:"(0~=?z_hbj)"
        assume z_Heh:"(~((a_VARIABLEunde_flagunde_a[?z_hbj]) \\in {?z_hk, FALSE}))" (is "~?z_hei")
        show FALSE
        by (rule notE [OF z_Heg z_Heb])
       next
        assume z_Hbh:"(~?z_hbi)"
        show FALSE
        by (rule notE [OF z_Hbh z_Hbi])
       qed
      next
       assume z_Hbi:"(?z_hbj \\in ?z_hbg)" (is "?z_hbi")
       assume z_Heg:"(0~=?z_hbj)"
       assume z_Hbw:"(?z_hbx~=(a_VARIABLEunde_flagunde_a[?z_hbj]))" (is "_~=?z_hby")
       show FALSE
       by (rule zenon_L4_ [OF z_Hbw z_Hbz])
      next
       assume z_Hbh:"(~(?z_hbj \\in ?z_hbg))" (is "~?z_hbi")
       show FALSE
       by (rule zenon_L3_ [OF z_Hbf z_Hbh z_Hbq])
      qed
     qed
     have z_Hcv: "?z_hcv"
     by (rule subst [where P="(\<lambda>zenon_Vha. (zenon_Vha \\in {TRUE, FALSE}))", OF z_Hdr], fact z_Hdh)
     thus "?z_hcv" .
    qed
   qed
  next
   assume z_Hen:"((CHOOSE x:(~((x \\in {0, 1})=>((a_VARIABLEunde_flagunde_hash_primea[x]) \\in {TRUE, FALSE})))) \\in {})" (is "?z_hen")
   show FALSE
   by (rule zenon_in_emptyset [of "(CHOOSE x:(~((x \\in {0, 1})=>((a_VARIABLEunde_flagunde_hash_primea[x]) \\in {TRUE, FALSE}))))", OF z_Hen])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 13"; *} qed
lemma ob'17:
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_VARIABLEunde_turnunde_a a_VARIABLEunde_turnunde_a'
fixes a_VARIABLEunde_processStateunde_a a_VARIABLEunde_processStateunde_a'
fixes a_VARIABLEunde_flagunde_a a_VARIABLEunde_flagunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_ProcessRequestFlag_ suppressed *)
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
(* usable definition STATE_critReqs_ suppressed *)
(* usable definition STATE_requestReqs_ suppressed *)
(* usable definition STATE_waitReqs_ suppressed *)
(* usable definition STATE_I_ suppressed *)
(* usable definition TEMPORAL_MutExSpec_ suppressed *)
(* usable definition TEMPORAL_TestSpec_ suppressed *)
(* usable definition STATE_InvImpMutEx_ suppressed *)
assumes v'31: "(((((a_VARIABLEunde_turnunde_a) \<in> ({((0)), ((Succ[0]))}))) & (((a_VARIABLEunde_flagunde_a) \<in> ([({((0)), ((Succ[0]))}) \<rightarrow> ({(TRUE), (FALSE)})]))) & (((a_VARIABLEunde_processStateunde_a) \<in> ([({((0)), ((Succ[0]))}) \<rightarrow> ({(''idle''), (''sentRequest''), (''waiting''), (''critical'')})])))) & (a_STATEunde_Iunde_a) & (a_STATEunde_MutualExclusionunde_a))"
assumes v'32: "((a_ACTIONunde_ProcessRequestFlagunde_a (((0)))))"
shows "(\<forall> a_CONSTANTunde_punde_a \<in> ({((0)), ((Succ[0]))}) : (((fapply ((a_VARIABLEunde_flagunde_a), (a_CONSTANTunde_punde_a))) \<in> ({(TRUE), (FALSE)}))))"(is "PROP ?ob'17")
proof -
ML_command {* writeln "*** TLAPS ENTER 17"; *}
show "PROP ?ob'17"

(* BEGIN ZENON INPUT
;; file=.tlacache/PetersonLemmas.tlaps/tlapm_df5a35.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/PetersonLemmas.tlaps/tlapm_df5a35.znn.out
;; obligation #17
$hyp "v'31" (/\ (/\ (TLA.in a_VARIABLEunde_turnunde_a
(TLA.set 0 (TLA.fapply TLA.Succ 0))) (TLA.in a_VARIABLEunde_flagunde_a
(TLA.FuncSet (TLA.set 0 (TLA.fapply TLA.Succ 0)) (TLA.set T. F.)))
(TLA.in a_VARIABLEunde_processStateunde_a
(TLA.FuncSet (TLA.set 0 (TLA.fapply TLA.Succ 0)) (TLA.set "idle" "sentRequest" "waiting" "critical"))))
a_STATEunde_Iunde_a
a_STATEunde_MutualExclusionunde_a)
$hyp "v'32" (a_ACTIONunde_ProcessRequestFlagunde_a 0)
$goal (TLA.bAll (TLA.set 0 (TLA.fapply TLA.Succ 0)) ((a_CONSTANTunde_punde_a) (TLA.in (TLA.fapply a_VARIABLEunde_flagunde_a a_CONSTANTunde_punde_a)
(TLA.set T. F.))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(((a_VARIABLEunde_turnunde_a \\in {0, 1})&((a_VARIABLEunde_flagunde_a \\in FuncSet({0, 1}, {TRUE, FALSE}))&(a_VARIABLEunde_processStateunde_a \\in FuncSet({0, 1}, {''idle'', ''sentRequest'', ''waiting'', ''critical''}))))&(a_STATEunde_Iunde_a&a_STATEunde_MutualExclusionunde_a))" (is "?z_hd&?z_hy")
 using v'31 by blast
 assume z_Hc:"(~bAll({0, 1}, (\<lambda>a_CONSTANTunde_punde_a. ((a_VARIABLEunde_flagunde_a[a_CONSTANTunde_punde_a]) \\in {TRUE, FALSE}))))" (is "~?z_hbb")
 have z_Hd: "?z_hd" (is "?z_he&?z_hj")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hj: "?z_hj" (is "?z_hk&?z_hq")
 by (rule zenon_and_1 [OF z_Hd])
 have z_Hk: "?z_hk"
 by (rule zenon_and_0 [OF z_Hj])
 have z_Hbg_z_Hc: "(~(\\A x:((x \\in {0, 1})=>((a_VARIABLEunde_flagunde_a[x]) \\in {TRUE, FALSE})))) == (~?z_hbb)" (is "?z_hbg == ?z_hc")
 by (unfold bAll_def)
 have z_Hbg: "?z_hbg" (is "~(\\A x : ?z_hbn(x))")
 by (unfold z_Hbg_z_Hc, fact z_Hc)
 have z_Hbh: "(\\A x:((x \\in {0, 1})=>((a_VARIABLEunde_flagunde_a[x]) \\in {TRUE, FALSE})))"
 by (rule zenon_in_funcset_2 [of "a_VARIABLEunde_flagunde_a" "{0, 1}" "{TRUE, FALSE}", OF z_Hk])
 show FALSE
 by (rule notE [OF z_Hbg z_Hbh])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 17"; *} qed
lemma ob'19:
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_VARIABLEunde_turnunde_a a_VARIABLEunde_turnunde_a'
fixes a_VARIABLEunde_processStateunde_a a_VARIABLEunde_processStateunde_a'
fixes a_VARIABLEunde_flagunde_a a_VARIABLEunde_flagunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_ProcessRequestFlag_ suppressed *)
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
(* usable definition STATE_critReqs_ suppressed *)
(* usable definition STATE_requestReqs_ suppressed *)
(* usable definition STATE_waitReqs_ suppressed *)
(* usable definition STATE_I_ suppressed *)
(* usable definition TEMPORAL_MutExSpec_ suppressed *)
(* usable definition TEMPORAL_TestSpec_ suppressed *)
(* usable definition STATE_InvImpMutEx_ suppressed *)
assumes v'31: "(((((a_VARIABLEunde_turnunde_a) \<in> ({((0)), ((Succ[0]))}))) & (((a_VARIABLEunde_flagunde_a) \<in> ([({((0)), ((Succ[0]))}) \<rightarrow> ({(TRUE), (FALSE)})]))) & (((a_VARIABLEunde_processStateunde_a) \<in> ([({((0)), ((Succ[0]))}) \<rightarrow> ({(''idle''), (''sentRequest''), (''waiting''), (''critical'')})])))) & (a_STATEunde_Iunde_a) & (a_STATEunde_MutualExclusionunde_a))"
assumes v'32: "((a_ACTIONunde_ProcessRequestFlagunde_a (((0)))))"
assumes v'45: "((((a_VARIABLEunde_flagunde_hash_primea :: c)) = ([(a_VARIABLEunde_flagunde_a) EXCEPT ![((0))] = (TRUE)])))"
shows "((((a_VARIABLEunde_flagunde_hash_primea :: c)) \<in> ([({((0)), ((Succ[0]))}) \<rightarrow> ({(TRUE), (FALSE)})])))"(is "PROP ?ob'19")
proof -
ML_command {* writeln "*** TLAPS ENTER 19"; *}
show "PROP ?ob'19"

(* BEGIN ZENON INPUT
;; file=.tlacache/PetersonLemmas.tlaps/tlapm_4b2d40.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/PetersonLemmas.tlaps/tlapm_4b2d40.znn.out
;; obligation #19
$hyp "v'31" (/\ (/\ (TLA.in a_VARIABLEunde_turnunde_a
(TLA.set 0 (TLA.fapply TLA.Succ 0))) (TLA.in a_VARIABLEunde_flagunde_a
(TLA.FuncSet (TLA.set 0 (TLA.fapply TLA.Succ 0)) (TLA.set T. F.)))
(TLA.in a_VARIABLEunde_processStateunde_a
(TLA.FuncSet (TLA.set 0 (TLA.fapply TLA.Succ 0)) (TLA.set "idle" "sentRequest" "waiting" "critical"))))
a_STATEunde_Iunde_a
a_STATEunde_MutualExclusionunde_a)
$hyp "v'32" (a_ACTIONunde_ProcessRequestFlagunde_a 0)
$hyp "v'45" (= a_VARIABLEunde_flagunde_hash_primea
(TLA.except a_VARIABLEunde_flagunde_a 0 T.))
$goal (TLA.in a_VARIABLEunde_flagunde_hash_primea
(TLA.FuncSet (TLA.set 0 (TLA.fapply TLA.Succ 0)) (TLA.set T. F.)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(((a_VARIABLEunde_turnunde_a \\in {0, 1})&((a_VARIABLEunde_flagunde_a \\in FuncSet({0, 1}, {TRUE, FALSE}))&(a_VARIABLEunde_processStateunde_a \\in FuncSet({0, 1}, {''idle'', ''sentRequest'', ''waiting'', ''critical''}))))&(a_STATEunde_Iunde_a&a_STATEunde_MutualExclusionunde_a))" (is "?z_he&?z_hz")
 using v'31 by blast
 have z_Hc:"(a_VARIABLEunde_flagunde_hash_primea=except(a_VARIABLEunde_flagunde_a, 0, TRUE))" (is "_=?z_hbd")
 using v'45 by blast
 assume z_Hd:"(~(a_VARIABLEunde_flagunde_hash_primea \\in FuncSet({0, 1}, {TRUE, FALSE})))" (is "~?z_hbe")
 have z_He: "?z_he" (is "?z_hf&?z_hk")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hk: "?z_hk" (is "?z_hl&?z_hr")
 by (rule zenon_and_1 [OF z_He])
 have z_Hl: "?z_hl"
 by (rule zenon_and_0 [OF z_Hk])
 have z_Hbf: "(~(?z_hbd \\in FuncSet({0, 1}, {TRUE, FALSE})))" (is "~?z_hbg")
 by (rule subst [where P="(\<lambda>zenon_Vf. (~(zenon_Vf \\in FuncSet({0, 1}, {TRUE, FALSE}))))", OF z_Hc z_Hd])
 show FALSE
 proof (rule zenon_except_notin_funcset [of "a_VARIABLEunde_flagunde_a" "0" "TRUE" "{0, 1}" "{TRUE, FALSE}", OF z_Hbf])
  assume z_Hbl:"(~?z_hl)"
  show FALSE
  by (rule notE [OF z_Hbl z_Hl])
 next
  assume z_Hbm:"(~(TRUE \\in {TRUE, FALSE}))" (is "~?z_hbn")
  have z_Hbo: "(TRUE~=TRUE)" (is "?z_hp~=_")
  by (rule zenon_notin_addElt_0 [of "?z_hp" "?z_hp" "{FALSE}", OF z_Hbm])
  show FALSE
  by (rule zenon_noteq [OF z_Hbo])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 19"; *} qed
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
(* usable definition STATE_critReqs_ suppressed *)
(* usable definition STATE_requestReqs_ suppressed *)
(* usable definition STATE_waitReqs_ suppressed *)
(* usable definition STATE_I_ suppressed *)
(* usable definition TEMPORAL_MutExSpec_ suppressed *)
(* usable definition TEMPORAL_TestSpec_ suppressed *)
(* usable definition STATE_InvImpMutEx_ suppressed *)
assumes v'30: "(((((a_VARIABLEunde_turnunde_a) \<in> ({((0)), ((Succ[0]))}))) & (((a_VARIABLEunde_flagunde_a) \<in> ([({((0)), ((Succ[0]))}) \<rightarrow> ({(TRUE), (FALSE)})]))) & (((a_VARIABLEunde_processStateunde_a) \<in> ([({((0)), ((Succ[0]))}) \<rightarrow> ({(''idle''), (''sentRequest''), (''waiting''), (''critical'')})])))) & (a_STATEunde_Iunde_a) & (a_STATEunde_MutualExclusionunde_a))"
assumes v'31: "(((fapply ((a_VARIABLEunde_processStateunde_a), ((0)))) = (''idle'')))"
assumes v'32: "((((a_VARIABLEunde_flagunde_hash_primea :: c)) = ([(a_VARIABLEunde_flagunde_a) EXCEPT ![((0))] = (TRUE)])))"
assumes v'33: "((((a_VARIABLEunde_processStateunde_hash_primea :: c)) = ([(a_VARIABLEunde_processStateunde_a) EXCEPT ![((0))] = (''sentRequest'')])))"
assumes v'34: "((((a_VARIABLEunde_turnunde_hash_primea :: c)) = (a_VARIABLEunde_turnunde_a)))"
assumes v'43: "((((a_VARIABLEunde_turnunde_a) \<in> ({((0)), ((Succ[0]))}))) & (((a_VARIABLEunde_flagunde_a) \<in> ([({((0)), ((Succ[0]))}) \<rightarrow> ({(TRUE), (FALSE)})]))) & (((a_VARIABLEunde_processStateunde_a) \<in> ([({((0)), ((Succ[0]))}) \<rightarrow> ({(''idle''), (''sentRequest''), (''waiting''), (''critical'')})]))))"
assumes v'44: "((((a_VARIABLEunde_turnunde_hash_primea :: c)) \<in> ({((0)), ((Succ[0]))})))"
assumes v'45: "(\<forall> a_CONSTANTunde_punde_a \<in> ({((0)), ((Succ[0]))}) : (((fapply (((a_VARIABLEunde_flagunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<in> ({(TRUE), (FALSE)}))))"
assumes v'46: "((((a_VARIABLEunde_processStateunde_hash_primea :: c)) \<in> ([({((0)), ((Succ[0]))}) \<rightarrow> ({(''idle''), (''sentRequest''), (''waiting''), (''critical'')})])))"
shows "(((((a_VARIABLEunde_turnunde_hash_primea :: c)) \<in> ({((0)), ((Succ[0]))}))) & ((((a_VARIABLEunde_flagunde_hash_primea :: c)) \<in> ([({((0)), ((Succ[0]))}) \<rightarrow> ({(TRUE), (FALSE)})]))) & ((((a_VARIABLEunde_processStateunde_hash_primea :: c)) \<in> ([({((0)), ((Succ[0]))}) \<rightarrow> ({(''idle''), (''sentRequest''), (''waiting''), (''critical'')})]))))"(is "PROP ?ob'6")
proof -
ML_command {* writeln "*** TLAPS ENTER 6"; *}
show "PROP ?ob'6"

(* BEGIN ZENON INPUT
;; file=.tlacache/PetersonLemmas.tlaps/tlapm_d5374d.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/PetersonLemmas.tlaps/tlapm_d5374d.znn.out
;; obligation #6
$hyp "v'30" (/\ (/\ (TLA.in a_VARIABLEunde_turnunde_a
(TLA.set 0 (TLA.fapply TLA.Succ 0))) (TLA.in a_VARIABLEunde_flagunde_a
(TLA.FuncSet (TLA.set 0 (TLA.fapply TLA.Succ 0)) (TLA.set T. F.)))
(TLA.in a_VARIABLEunde_processStateunde_a
(TLA.FuncSet (TLA.set 0 (TLA.fapply TLA.Succ 0)) (TLA.set "idle" "sentRequest" "waiting" "critical"))))
a_STATEunde_Iunde_a
a_STATEunde_MutualExclusionunde_a)
$hyp "v'31" (= (TLA.fapply a_VARIABLEunde_processStateunde_a 0)
"idle")
$hyp "v'32" (= a_VARIABLEunde_flagunde_hash_primea
(TLA.except a_VARIABLEunde_flagunde_a 0 T.))
$hyp "v'33" (= a_VARIABLEunde_processStateunde_hash_primea
(TLA.except a_VARIABLEunde_processStateunde_a 0 "sentRequest"))
$hyp "v'34" (= a_VARIABLEunde_turnunde_hash_primea
a_VARIABLEunde_turnunde_a)
$hyp "v'43" (/\ (TLA.in a_VARIABLEunde_turnunde_a
(TLA.set 0 (TLA.fapply TLA.Succ 0))) (TLA.in a_VARIABLEunde_flagunde_a
(TLA.FuncSet (TLA.set 0 (TLA.fapply TLA.Succ 0)) (TLA.set T. F.)))
(TLA.in a_VARIABLEunde_processStateunde_a
(TLA.FuncSet (TLA.set 0 (TLA.fapply TLA.Succ 0)) (TLA.set "idle" "sentRequest" "waiting" "critical"))))
$hyp "v'44" (TLA.in a_VARIABLEunde_turnunde_hash_primea
(TLA.set 0 (TLA.fapply TLA.Succ 0)))
$hyp "v'45" (TLA.bAll (TLA.set 0 (TLA.fapply TLA.Succ 0)) ((a_CONSTANTunde_punde_a) (TLA.in (TLA.fapply a_VARIABLEunde_flagunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.set T. F.))))
$hyp "v'46" (TLA.in a_VARIABLEunde_processStateunde_hash_primea
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
 have z_Ha:"(((a_VARIABLEunde_turnunde_a \\in {0, 1})&((a_VARIABLEunde_flagunde_a \\in FuncSet({0, 1}, {TRUE, FALSE}))&(a_VARIABLEunde_processStateunde_a \\in FuncSet({0, 1}, {''idle'', ''sentRequest'', ''waiting'', ''critical''}))))&(a_STATEunde_Iunde_a&a_STATEunde_MutualExclusionunde_a))" (is "?z_hf&?z_hbe")
 using v'30 by blast
 have z_Hg:"(a_VARIABLEunde_turnunde_hash_primea \\in {0, 1})" (is "?z_hg")
 using v'44 by blast
 have z_Hc:"(a_VARIABLEunde_flagunde_hash_primea=except(a_VARIABLEunde_flagunde_a, 0, TRUE))" (is "_=?z_hbj")
 using v'32 by blast
 have z_Hi:"(a_VARIABLEunde_processStateunde_hash_primea \\in FuncSet({0, 1}, {''idle'', ''sentRequest'', ''waiting'', ''critical''}))" (is "?z_hi")
 using v'46 by blast
 assume z_Hj:"(~(?z_hg&((a_VARIABLEunde_flagunde_hash_primea \\in FuncSet({0, 1}, {TRUE, FALSE}))&?z_hi)))" (is "~(_&?z_hbm)")
 have z_Hf: "?z_hf" (is "?z_hk&?z_hp")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hp: "?z_hp" (is "?z_hq&?z_hw")
 by (rule zenon_and_1 [OF z_Hf])
 have z_Hq: "?z_hq"
 by (rule zenon_and_0 [OF z_Hp])
 show FALSE
 proof (rule zenon_notand [OF z_Hj])
  assume z_Hbo:"(~?z_hg)"
  show FALSE
  by (rule notE [OF z_Hbo z_Hg])
 next
  assume z_Hbp:"(~?z_hbm)" (is "~(?z_hbn&_)")
  show FALSE
  proof (rule zenon_notand [OF z_Hbp])
   assume z_Hbq:"(~?z_hbn)"
   have z_Hbr: "(~(?z_hbj \\in FuncSet({0, 1}, {TRUE, FALSE})))" (is "~?z_hbs")
   by (rule subst [where P="(\<lambda>zenon_Vca. (~(zenon_Vca \\in FuncSet({0, 1}, {TRUE, FALSE}))))", OF z_Hc z_Hbq])
   show FALSE
   proof (rule zenon_except_notin_funcset [of "a_VARIABLEunde_flagunde_a" "0" "TRUE" "{0, 1}" "{TRUE, FALSE}", OF z_Hbr])
    assume z_Hbx:"(~?z_hq)"
    show FALSE
    by (rule notE [OF z_Hbx z_Hq])
   next
    assume z_Hby:"(~(TRUE \\in {TRUE, FALSE}))" (is "~?z_hbz")
    have z_Hca: "(TRUE~=TRUE)" (is "?z_hu~=_")
    by (rule zenon_notin_addElt_0 [of "?z_hu" "?z_hu" "{FALSE}", OF z_Hby])
    show FALSE
    by (rule zenon_noteq [OF z_Hca])
   qed
  next
   assume z_Hcc:"(~?z_hi)"
   show FALSE
   by (rule notE [OF z_Hcc z_Hi])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 6"; *} qed
lemma ob'38:
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_VARIABLEunde_turnunde_a a_VARIABLEunde_turnunde_a'
fixes a_VARIABLEunde_processStateunde_a a_VARIABLEunde_processStateunde_a'
fixes a_VARIABLEunde_flagunde_a a_VARIABLEunde_flagunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_ProcessRequestFlag_ suppressed *)
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
(* usable definition STATE_critReqs_ suppressed *)
(* usable definition STATE_requestReqs_ suppressed *)
(* usable definition STATE_waitReqs_ suppressed *)
(* usable definition STATE_I_ suppressed *)
(* usable definition STATE_Inv_ suppressed *)
(* usable definition TEMPORAL_MutExSpec_ suppressed *)
(* usable definition TEMPORAL_TestSpec_ suppressed *)
(* usable definition STATE_InvImpMutEx_ suppressed *)
assumes v'33: "(a_STATEunde_Invunde_a)"
assumes v'34: "((a_ACTIONunde_ProcessRequestFlagunde_a (((0)))))"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> ({((0)), ((Succ[0]))}))"
fixes a_CONSTANTunde_qunde_a
assumes a_CONSTANTunde_qunde_a_in : "(a_CONSTANTunde_qunde_a \<in> ({((0)), ((Succ[0]))}))"
assumes v'53: "(((((((a_CONSTANTunde_punde_a) = ((0)))) \<and> (((a_CONSTANTunde_qunde_a) = ((Succ[0])))))) \<or> (((((a_CONSTANTunde_punde_a) = ((Succ[0])))) \<and> (((a_CONSTANTunde_qunde_a) = ((0))))))))"
assumes v'54: "(((((((a_CONSTANTunde_punde_a) = ((0)))) \<and> (((a_CONSTANTunde_qunde_a) = ((Succ[0])))))) \<Longrightarrow> (((((((((fapply (((a_VARIABLEunde_flagunde_hash_primea :: c)), (a_CONSTANTunde_qunde_a))) = (FALSE))) \<or> ((((a_VARIABLEunde_turnunde_hash_primea :: c)) = (a_CONSTANTunde_punde_a))))) \<or> (((fapply (((a_VARIABLEunde_processStateunde_hash_primea :: c)), (a_CONSTANTunde_qunde_a))) = (''sentRequest''))))) \<and> (((fapply (((a_VARIABLEunde_flagunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = (TRUE)))))))"
assumes v'55: "(((((((a_CONSTANTunde_punde_a) = ((Succ[0])))) \<and> (((a_CONSTANTunde_qunde_a) = ((0)))))) \<Longrightarrow> (((((((((fapply (((a_VARIABLEunde_flagunde_hash_primea :: c)), (a_CONSTANTunde_qunde_a))) = (FALSE))) \<or> ((((a_VARIABLEunde_turnunde_hash_primea :: c)) = (a_CONSTANTunde_punde_a))))) \<or> (((fapply (((a_VARIABLEunde_processStateunde_hash_primea :: c)), (a_CONSTANTunde_qunde_a))) = (''sentRequest''))))) \<and> (((fapply (((a_VARIABLEunde_flagunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = (TRUE)))))))"
shows "(((((((((fapply (((a_VARIABLEunde_flagunde_hash_primea :: c)), (a_CONSTANTunde_qunde_a))) = (FALSE))) \<or> ((((a_VARIABLEunde_turnunde_hash_primea :: c)) = (a_CONSTANTunde_punde_a))))) \<or> (((fapply (((a_VARIABLEunde_processStateunde_hash_primea :: c)), (a_CONSTANTunde_qunde_a))) = (''sentRequest''))))) \<and> (((fapply (((a_VARIABLEunde_flagunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = (TRUE)))))"(is "PROP ?ob'38")
proof -
ML_command {* writeln "*** TLAPS ENTER 38"; *}
show "PROP ?ob'38"

(* BEGIN ZENON INPUT
;; file=.tlacache/PetersonLemmas.tlaps/tlapm_e9b954.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/PetersonLemmas.tlaps/tlapm_e9b954.znn.out
;; obligation #38
$hyp "v'33" a_STATEunde_Invunde_a
$hyp "v'34" (a_ACTIONunde_ProcessRequestFlagunde_a 0)
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a (TLA.set 0 (TLA.fapply TLA.Succ 0)))
$hyp "a_CONSTANTunde_qunde_a_in" (TLA.in a_CONSTANTunde_qunde_a (TLA.set 0 (TLA.fapply TLA.Succ 0)))
$hyp "v'53" (\/ (/\ (= a_CONSTANTunde_punde_a 0) (= a_CONSTANTunde_qunde_a
(TLA.fapply TLA.Succ 0))) (/\ (= a_CONSTANTunde_punde_a
(TLA.fapply TLA.Succ 0)) (= a_CONSTANTunde_qunde_a
0)))
$hyp "v'54" (=> (/\ (= a_CONSTANTunde_punde_a 0) (= a_CONSTANTunde_qunde_a
(TLA.fapply TLA.Succ 0))) (/\ (\/ (\/ (= (TLA.fapply a_VARIABLEunde_flagunde_hash_primea a_CONSTANTunde_qunde_a)
F.) (= a_VARIABLEunde_turnunde_hash_primea a_CONSTANTunde_punde_a))
(= (TLA.fapply a_VARIABLEunde_processStateunde_hash_primea a_CONSTANTunde_qunde_a)
"sentRequest"))
(= (TLA.fapply a_VARIABLEunde_flagunde_hash_primea a_CONSTANTunde_punde_a)
T.)))
$hyp "v'55" (=> (/\ (= a_CONSTANTunde_punde_a (TLA.fapply TLA.Succ 0))
(= a_CONSTANTunde_qunde_a
0)) (/\ (\/ (\/ (= (TLA.fapply a_VARIABLEunde_flagunde_hash_primea a_CONSTANTunde_qunde_a)
F.) (= a_VARIABLEunde_turnunde_hash_primea a_CONSTANTunde_punde_a))
(= (TLA.fapply a_VARIABLEunde_processStateunde_hash_primea a_CONSTANTunde_qunde_a)
"sentRequest"))
(= (TLA.fapply a_VARIABLEunde_flagunde_hash_primea a_CONSTANTunde_punde_a)
T.)))
$goal (/\ (\/ (\/ (= (TLA.fapply a_VARIABLEunde_flagunde_hash_primea a_CONSTANTunde_qunde_a)
F.) (= a_VARIABLEunde_turnunde_hash_primea a_CONSTANTunde_punde_a))
(= (TLA.fapply a_VARIABLEunde_processStateunde_hash_primea a_CONSTANTunde_qunde_a)
"sentRequest"))
(= (TLA.fapply a_VARIABLEunde_flagunde_hash_primea a_CONSTANTunde_punde_a)
T.))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_He:"(((a_CONSTANTunde_punde_a=0)&(a_CONSTANTunde_qunde_a=1))|((a_CONSTANTunde_punde_a=1)&(a_CONSTANTunde_qunde_a=0)))" (is "?z_hi|?z_hp")
 using v'53 by blast
 have z_Hg:"(?z_hp=>(((((a_VARIABLEunde_flagunde_hash_primea[a_CONSTANTunde_qunde_a])=FALSE)|(a_VARIABLEunde_turnunde_hash_primea=a_CONSTANTunde_punde_a))|((a_VARIABLEunde_processStateunde_hash_primea[a_CONSTANTunde_qunde_a])=''sentRequest''))&((a_VARIABLEunde_flagunde_hash_primea[a_CONSTANTunde_punde_a])=TRUE)))" (is "_=>?z_hs")
 using v'55 by blast
 have z_Hf:"(?z_hi=>?z_hs)"
 using v'54 by blast
 have zenon_L1_: "(?z_hi=>?z_hs) ==> (a_CONSTANTunde_qunde_a=1) ==> (a_CONSTANTunde_punde_a=0) ==> (~?z_hs) ==> FALSE" (is "?z_hf ==> ?z_hm ==> ?z_hj ==> ?z_hh ==> FALSE")
 proof -
  assume z_Hf:"?z_hf"
  assume z_Hm:"?z_hm" (is "_=?z_ho")
  assume z_Hj:"?z_hj"
  assume z_Hh:"?z_hh" (is "~(?z_ht&?z_hbf)")
  show FALSE
  proof (rule zenon_imply [OF z_Hf])
   assume z_Hbi:"(~?z_hi)"
   show FALSE
   proof (rule zenon_notand [OF z_Hbi])
    assume z_Hbj:"(a_CONSTANTunde_punde_a~=0)"
    show FALSE
    by (rule notE [OF z_Hbj z_Hj])
   next
    assume z_Hbk:"(a_CONSTANTunde_qunde_a~=?z_ho)"
    show FALSE
    by (rule notE [OF z_Hbk z_Hm])
   qed
  next
   assume z_Hs:"?z_hs"
   show FALSE
   by (rule notE [OF z_Hh z_Hs])
  qed
 qed
 have zenon_L2_: "?z_hi ==> (a_CONSTANTunde_qunde_a=1) ==> (~?z_hs) ==> (?z_hi=>?z_hs) ==> FALSE" (is "_ ==> ?z_hm ==> ?z_hh ==> ?z_hf ==> FALSE")
 proof -
  assume z_Hi:"?z_hi" (is "?z_hj&_")
  assume z_Hm:"?z_hm" (is "_=?z_ho")
  assume z_Hh:"?z_hh" (is "~(?z_ht&?z_hbf)")
  assume z_Hf:"?z_hf"
  have z_Hj: "?z_hj"
  by (rule zenon_and_0 [OF z_Hi])
  have z_Hm: "?z_hm"
  by (rule zenon_and_1 [OF z_Hi])
  show FALSE
  by (rule zenon_L1_ [OF z_Hf z_Hm z_Hj z_Hh])
 qed
 have zenon_L3_: "(?z_hp=>?z_hs) ==> (a_CONSTANTunde_qunde_a=0) ==> (a_CONSTANTunde_punde_a=1) ==> (~?z_hs) ==> FALSE" (is "?z_hg ==> ?z_hr ==> ?z_hq ==> ?z_hh ==> FALSE")
 proof -
  assume z_Hg:"?z_hg"
  assume z_Hr:"?z_hr"
  assume z_Hq:"?z_hq" (is "_=?z_ho")
  assume z_Hh:"?z_hh" (is "~(?z_ht&?z_hbf)")
  show FALSE
  proof (rule zenon_imply [OF z_Hg])
   assume z_Hbl:"(~?z_hp)"
   show FALSE
   proof (rule zenon_notand [OF z_Hbl])
    assume z_Hbm:"(a_CONSTANTunde_punde_a~=?z_ho)"
    show FALSE
    by (rule notE [OF z_Hbm z_Hq])
   next
    assume z_Hbn:"(a_CONSTANTunde_qunde_a~=0)"
    show FALSE
    by (rule notE [OF z_Hbn z_Hr])
   qed
  next
   assume z_Hs:"?z_hs"
   show FALSE
   by (rule notE [OF z_Hh z_Hs])
  qed
 qed
 have zenon_L4_: "?z_hp ==> (a_CONSTANTunde_punde_a=1) ==> (~?z_hs) ==> (?z_hp=>?z_hs) ==> FALSE" (is "_ ==> ?z_hq ==> ?z_hh ==> ?z_hg ==> FALSE")
 proof -
  assume z_Hp:"?z_hp" (is "_&?z_hr")
  assume z_Hq:"?z_hq" (is "_=?z_ho")
  assume z_Hh:"?z_hh" (is "~(?z_ht&?z_hbf)")
  assume z_Hg:"?z_hg"
  have z_Hq: "?z_hq"
  by (rule zenon_and_0 [OF z_Hp])
  have z_Hr: "?z_hr"
  by (rule zenon_and_1 [OF z_Hp])
  show FALSE
  by (rule zenon_L3_ [OF z_Hg z_Hr z_Hq z_Hh])
 qed
 assume z_Hh:"(~?z_hs)" (is "~(?z_ht&?z_hbf)")
 show FALSE
 proof (rule zenon_or [OF z_He])
  assume z_Hi:"?z_hi" (is "?z_hj&?z_hm")
  have z_Hm: "?z_hm" (is "_=?z_ho")
  by (rule zenon_and_1 [OF z_Hi])
  show FALSE
  by (rule zenon_L2_ [OF z_Hi z_Hm z_Hh z_Hf])
 next
  assume z_Hp:"?z_hp" (is "?z_hq&?z_hr")
  have z_Hq: "?z_hq" (is "_=?z_ho")
  by (rule zenon_and_0 [OF z_Hp])
  show FALSE
  by (rule zenon_L4_ [OF z_Hp z_Hq z_Hh z_Hg])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 38"; *} qed
lemma ob'42:
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_VARIABLEunde_turnunde_a a_VARIABLEunde_turnunde_a'
fixes a_VARIABLEunde_processStateunde_a a_VARIABLEunde_processStateunde_a'
fixes a_VARIABLEunde_flagunde_a a_VARIABLEunde_flagunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_ProcessRequestFlag_ suppressed *)
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
(* usable definition STATE_requestReqs_ suppressed *)
(* usable definition STATE_waitReqs_ suppressed *)
(* usable definition STATE_I_ suppressed *)
(* usable definition STATE_Inv_ suppressed *)
(* usable definition TEMPORAL_MutExSpec_ suppressed *)
(* usable definition TEMPORAL_TestSpec_ suppressed *)
(* usable definition STATE_InvImpMutEx_ suppressed *)
assumes v'32: "(a_STATEunde_Invunde_a)"
assumes v'33: "((a_ACTIONunde_ProcessRequestFlagunde_a (((0)))))"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> ({((0)), ((Succ[0]))}))"
fixes a_CONSTANTunde_qunde_a
assumes a_CONSTANTunde_qunde_a_in : "(a_CONSTANTunde_qunde_a \<in> ({((0)), ((Succ[0]))}))"
assumes v'46: "(((((((a_CONSTANTunde_punde_a) \<noteq> (a_CONSTANTunde_qunde_a))) \<and> (((fapply (((a_VARIABLEunde_processStateunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = (''critical''))))) \<Longrightarrow> (((((((((fapply (((a_VARIABLEunde_flagunde_hash_primea :: c)), (a_CONSTANTunde_qunde_a))) = (FALSE))) \<or> ((((a_VARIABLEunde_turnunde_hash_primea :: c)) = (a_CONSTANTunde_punde_a))))) \<or> (((fapply (((a_VARIABLEunde_processStateunde_hash_primea :: c)), (a_CONSTANTunde_qunde_a))) = (''sentRequest''))))) \<and> (((fapply (((a_VARIABLEunde_flagunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = (TRUE)))))))"
shows "(((((((a_CONSTANTunde_punde_a) \<noteq> (a_CONSTANTunde_qunde_a))) \<and> (((fapply (((a_VARIABLEunde_processStateunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = (''critical''))))) \<Rightarrow> ((((((((fapply (((a_VARIABLEunde_flagunde_hash_primea :: c)), (a_CONSTANTunde_qunde_a))) = (FALSE))) \<or> ((((a_VARIABLEunde_turnunde_hash_primea :: c)) = (a_CONSTANTunde_punde_a))))) \<or> (((fapply (((a_VARIABLEunde_processStateunde_hash_primea :: c)), (a_CONSTANTunde_qunde_a))) = (''sentRequest''))))) & (((fapply (((a_VARIABLEunde_flagunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = (TRUE))))))"(is "PROP ?ob'42")
proof -
ML_command {* writeln "*** TLAPS ENTER 42"; *}
show "PROP ?ob'42"

(* BEGIN ZENON INPUT
;; file=.tlacache/PetersonLemmas.tlaps/tlapm_a758cd.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/PetersonLemmas.tlaps/tlapm_a758cd.znn.out
;; obligation #42
$hyp "v'32" a_STATEunde_Invunde_a
$hyp "v'33" (a_ACTIONunde_ProcessRequestFlagunde_a 0)
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a (TLA.set 0 (TLA.fapply TLA.Succ 0)))
$hyp "a_CONSTANTunde_qunde_a_in" (TLA.in a_CONSTANTunde_qunde_a (TLA.set 0 (TLA.fapply TLA.Succ 0)))
$hyp "v'46" (=> (/\ (-. (= a_CONSTANTunde_punde_a a_CONSTANTunde_qunde_a))
(= (TLA.fapply a_VARIABLEunde_processStateunde_hash_primea a_CONSTANTunde_punde_a)
"critical")) (/\ (\/ (\/ (= (TLA.fapply a_VARIABLEunde_flagunde_hash_primea a_CONSTANTunde_qunde_a)
F.) (= a_VARIABLEunde_turnunde_hash_primea a_CONSTANTunde_punde_a))
(= (TLA.fapply a_VARIABLEunde_processStateunde_hash_primea a_CONSTANTunde_qunde_a)
"sentRequest"))
(= (TLA.fapply a_VARIABLEunde_flagunde_hash_primea a_CONSTANTunde_punde_a)
T.)))
$goal (=> (/\ (-. (= a_CONSTANTunde_punde_a a_CONSTANTunde_qunde_a))
(= (TLA.fapply a_VARIABLEunde_processStateunde_hash_primea a_CONSTANTunde_punde_a)
"critical"))
(/\ (\/ (\/ (= (TLA.fapply a_VARIABLEunde_flagunde_hash_primea a_CONSTANTunde_qunde_a)
F.) (= a_VARIABLEunde_turnunde_hash_primea a_CONSTANTunde_punde_a))
(= (TLA.fapply a_VARIABLEunde_processStateunde_hash_primea a_CONSTANTunde_qunde_a)
"sentRequest"))
(= (TLA.fapply a_VARIABLEunde_flagunde_hash_primea a_CONSTANTunde_punde_a)
T.)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_He:"(((a_CONSTANTunde_punde_a~=a_CONSTANTunde_qunde_a)&((a_VARIABLEunde_processStateunde_hash_primea[a_CONSTANTunde_punde_a])=''critical''))=>(((((a_VARIABLEunde_flagunde_hash_primea[a_CONSTANTunde_qunde_a])=FALSE)|(a_VARIABLEunde_turnunde_hash_primea=a_CONSTANTunde_punde_a))|((a_VARIABLEunde_processStateunde_hash_primea[a_CONSTANTunde_qunde_a])=''sentRequest''))&((a_VARIABLEunde_flagunde_hash_primea[a_CONSTANTunde_punde_a])=TRUE)))" (is "?z_hg=>?z_ho")
 using v'46 by blast
 assume z_Hf:"(~(?z_hg=>?z_ho))"
 show FALSE
 by (rule notE [OF z_Hf z_He])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 42"; *} qed
lemma ob'79:
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_VARIABLEunde_turnunde_a a_VARIABLEunde_turnunde_a'
fixes a_VARIABLEunde_processStateunde_a a_VARIABLEunde_processStateunde_a'
fixes a_VARIABLEunde_flagunde_a a_VARIABLEunde_flagunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_ProcessRequestFlag_ suppressed *)
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
(* usable definition STATE_critReqs_ suppressed *)
(* usable definition STATE_requestReqs_ suppressed *)
(* usable definition STATE_waitReqs_ suppressed *)
(* usable definition STATE_I_ suppressed *)
(* usable definition STATE_Inv_ suppressed *)
(* usable definition TEMPORAL_MutExSpec_ suppressed *)
(* usable definition TEMPORAL_TestSpec_ suppressed *)
(* usable definition STATE_InvImpMutEx_ suppressed *)
assumes v'33: "(a_STATEunde_Invunde_a)"
assumes v'34: "((a_ACTIONunde_ProcessRequestFlagunde_a (((0)))))"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> ({((0)), ((Succ[0]))}))"
fixes a_CONSTANTunde_qunde_a
assumes a_CONSTANTunde_qunde_a_in : "(a_CONSTANTunde_qunde_a \<in> ({((0)), ((Succ[0]))}))"
assumes v'54: "(((((((a_CONSTANTunde_punde_a) = ((0)))) \<and> (((a_CONSTANTunde_qunde_a) = ((Succ[0])))))) \<or> (((((a_CONSTANTunde_punde_a) = ((Succ[0])))) \<and> (((a_CONSTANTunde_qunde_a) = ((0))))))))"
assumes v'55: "(((((((a_CONSTANTunde_punde_a) = ((0)))) \<and> (((a_CONSTANTunde_qunde_a) = ((Succ[0])))))) \<Longrightarrow> (((fapply (((a_VARIABLEunde_flagunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = (TRUE)))))"
assumes v'56: "(((((((a_CONSTANTunde_punde_a) = ((Succ[0])))) \<and> (((a_CONSTANTunde_qunde_a) = ((0)))))) \<Longrightarrow> (((fapply (((a_VARIABLEunde_flagunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = (TRUE)))))"
shows "(((fapply (((a_VARIABLEunde_flagunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = (TRUE)))"(is "PROP ?ob'79")
proof -
ML_command {* writeln "*** TLAPS ENTER 79"; *}
show "PROP ?ob'79"

(* BEGIN ZENON INPUT
;; file=.tlacache/PetersonLemmas.tlaps/tlapm_644f9c.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/PetersonLemmas.tlaps/tlapm_644f9c.znn.out
;; obligation #79
$hyp "v'33" a_STATEunde_Invunde_a
$hyp "v'34" (a_ACTIONunde_ProcessRequestFlagunde_a 0)
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a (TLA.set 0 (TLA.fapply TLA.Succ 0)))
$hyp "a_CONSTANTunde_qunde_a_in" (TLA.in a_CONSTANTunde_qunde_a (TLA.set 0 (TLA.fapply TLA.Succ 0)))
$hyp "v'54" (\/ (/\ (= a_CONSTANTunde_punde_a 0) (= a_CONSTANTunde_qunde_a
(TLA.fapply TLA.Succ 0))) (/\ (= a_CONSTANTunde_punde_a
(TLA.fapply TLA.Succ 0)) (= a_CONSTANTunde_qunde_a
0)))
$hyp "v'55" (=> (/\ (= a_CONSTANTunde_punde_a 0) (= a_CONSTANTunde_qunde_a
(TLA.fapply TLA.Succ 0))) (= (TLA.fapply a_VARIABLEunde_flagunde_hash_primea a_CONSTANTunde_punde_a)
T.))
$hyp "v'56" (=> (/\ (= a_CONSTANTunde_punde_a (TLA.fapply TLA.Succ 0))
(= a_CONSTANTunde_qunde_a
0)) (= (TLA.fapply a_VARIABLEunde_flagunde_hash_primea a_CONSTANTunde_punde_a)
T.))
$goal (= (TLA.fapply a_VARIABLEunde_flagunde_hash_primea a_CONSTANTunde_punde_a)
T.)
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_He:"(((a_CONSTANTunde_punde_a=0)&(a_CONSTANTunde_qunde_a=1))|((a_CONSTANTunde_punde_a=1)&(a_CONSTANTunde_qunde_a=0)))" (is "?z_hi|?z_hp")
 using v'54 by blast
 have z_Hg:"(?z_hp=>((a_VARIABLEunde_flagunde_hash_primea[a_CONSTANTunde_punde_a])=TRUE))" (is "_=>?z_hs")
 using v'56 by blast
 have z_Hf:"(?z_hi=>?z_hs)"
 using v'55 by blast
 have zenon_L1_: "(?z_hi=>?z_hs) ==> (a_CONSTANTunde_qunde_a=1) ==> (a_CONSTANTunde_punde_a=0) ==> ((a_VARIABLEunde_flagunde_hash_primea[a_CONSTANTunde_punde_a])~=TRUE) ==> FALSE" (is "?z_hf ==> ?z_hm ==> ?z_hj ==> ?z_hh ==> FALSE")
 proof -
  assume z_Hf:"?z_hf"
  assume z_Hm:"?z_hm" (is "_=?z_ho")
  assume z_Hj:"?z_hj"
  assume z_Hh:"?z_hh" (is "?z_ht~=?z_hv")
  show FALSE
  proof (rule zenon_imply [OF z_Hf])
   assume z_Hw:"(~?z_hi)"
   show FALSE
   proof (rule zenon_notand [OF z_Hw])
    assume z_Hx:"(a_CONSTANTunde_punde_a~=0)"
    show FALSE
    by (rule notE [OF z_Hx z_Hj])
   next
    assume z_Hy:"(a_CONSTANTunde_qunde_a~=?z_ho)"
    show FALSE
    by (rule notE [OF z_Hy z_Hm])
   qed
  next
   assume z_Hs:"?z_hs"
   show FALSE
   by (rule notE [OF z_Hh z_Hs])
  qed
 qed
 have zenon_L2_: "?z_hi ==> (a_CONSTANTunde_qunde_a=1) ==> ((a_VARIABLEunde_flagunde_hash_primea[a_CONSTANTunde_punde_a])~=TRUE) ==> (?z_hi=>?z_hs) ==> FALSE" (is "_ ==> ?z_hm ==> ?z_hh ==> ?z_hf ==> FALSE")
 proof -
  assume z_Hi:"?z_hi" (is "?z_hj&_")
  assume z_Hm:"?z_hm" (is "_=?z_ho")
  assume z_Hh:"?z_hh" (is "?z_ht~=?z_hv")
  assume z_Hf:"?z_hf"
  have z_Hj: "?z_hj"
  by (rule zenon_and_0 [OF z_Hi])
  have z_Hm: "?z_hm"
  by (rule zenon_and_1 [OF z_Hi])
  show FALSE
  by (rule zenon_L1_ [OF z_Hf z_Hm z_Hj z_Hh])
 qed
 have zenon_L3_: "(?z_hp=>?z_hs) ==> (a_CONSTANTunde_qunde_a=0) ==> (a_CONSTANTunde_punde_a=1) ==> ((a_VARIABLEunde_flagunde_hash_primea[a_CONSTANTunde_punde_a])~=TRUE) ==> FALSE" (is "?z_hg ==> ?z_hr ==> ?z_hq ==> ?z_hh ==> FALSE")
 proof -
  assume z_Hg:"?z_hg"
  assume z_Hr:"?z_hr"
  assume z_Hq:"?z_hq" (is "_=?z_ho")
  assume z_Hh:"?z_hh" (is "?z_ht~=?z_hv")
  show FALSE
  proof (rule zenon_imply [OF z_Hg])
   assume z_Hz:"(~?z_hp)"
   show FALSE
   proof (rule zenon_notand [OF z_Hz])
    assume z_Hba:"(a_CONSTANTunde_punde_a~=?z_ho)"
    show FALSE
    by (rule notE [OF z_Hba z_Hq])
   next
    assume z_Hbb:"(a_CONSTANTunde_qunde_a~=0)"
    show FALSE
    by (rule notE [OF z_Hbb z_Hr])
   qed
  next
   assume z_Hs:"?z_hs"
   show FALSE
   by (rule notE [OF z_Hh z_Hs])
  qed
 qed
 have zenon_L4_: "?z_hp ==> (a_CONSTANTunde_punde_a=1) ==> ((a_VARIABLEunde_flagunde_hash_primea[a_CONSTANTunde_punde_a])~=TRUE) ==> (?z_hp=>?z_hs) ==> FALSE" (is "_ ==> ?z_hq ==> ?z_hh ==> ?z_hg ==> FALSE")
 proof -
  assume z_Hp:"?z_hp" (is "_&?z_hr")
  assume z_Hq:"?z_hq" (is "_=?z_ho")
  assume z_Hh:"?z_hh" (is "?z_ht~=?z_hv")
  assume z_Hg:"?z_hg"
  have z_Hq: "?z_hq"
  by (rule zenon_and_0 [OF z_Hp])
  have z_Hr: "?z_hr"
  by (rule zenon_and_1 [OF z_Hp])
  show FALSE
  by (rule zenon_L3_ [OF z_Hg z_Hr z_Hq z_Hh])
 qed
 assume z_Hh:"((a_VARIABLEunde_flagunde_hash_primea[a_CONSTANTunde_punde_a])~=TRUE)" (is "?z_ht~=?z_hv")
 show FALSE
 proof (rule zenon_or [OF z_He])
  assume z_Hi:"?z_hi" (is "?z_hj&?z_hm")
  have z_Hm: "?z_hm" (is "_=?z_ho")
  by (rule zenon_and_1 [OF z_Hi])
  show FALSE
  by (rule zenon_L2_ [OF z_Hi z_Hm z_Hh z_Hf])
 next
  assume z_Hp:"?z_hp" (is "?z_hq&?z_hr")
  have z_Hq: "?z_hq" (is "_=?z_ho")
  by (rule zenon_and_0 [OF z_Hp])
  show FALSE
  by (rule zenon_L4_ [OF z_Hp z_Hq z_Hh z_Hg])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 79"; *} qed
lemma ob'83:
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_VARIABLEunde_turnunde_a a_VARIABLEunde_turnunde_a'
fixes a_VARIABLEunde_processStateunde_a a_VARIABLEunde_processStateunde_a'
fixes a_VARIABLEunde_flagunde_a a_VARIABLEunde_flagunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_ProcessRequestFlag_ suppressed *)
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
(* usable definition STATE_critReqs_ suppressed *)
(* usable definition STATE_waitReqs_ suppressed *)
(* usable definition STATE_I_ suppressed *)
(* usable definition STATE_Inv_ suppressed *)
(* usable definition TEMPORAL_MutExSpec_ suppressed *)
(* usable definition TEMPORAL_TestSpec_ suppressed *)
(* usable definition STATE_InvImpMutEx_ suppressed *)
assumes v'32: "(a_STATEunde_Invunde_a)"
assumes v'33: "((a_ACTIONunde_ProcessRequestFlagunde_a (((0)))))"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> ({((0)), ((Succ[0]))}))"
fixes a_CONSTANTunde_qunde_a
assumes a_CONSTANTunde_qunde_a_in : "(a_CONSTANTunde_qunde_a \<in> ({((0)), ((Succ[0]))}))"
assumes v'47: "(((((((a_CONSTANTunde_punde_a) \<noteq> (a_CONSTANTunde_qunde_a))) \<and> (((fapply (((a_VARIABLEunde_processStateunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = (''sentRequest''))))) \<Longrightarrow> (((fapply (((a_VARIABLEunde_flagunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = (TRUE)))))"
shows "(((((((a_CONSTANTunde_punde_a) \<noteq> (a_CONSTANTunde_qunde_a))) \<and> (((fapply (((a_VARIABLEunde_processStateunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = (''sentRequest''))))) \<Rightarrow> (((fapply (((a_VARIABLEunde_flagunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = (TRUE)))))"(is "PROP ?ob'83")
proof -
ML_command {* writeln "*** TLAPS ENTER 83"; *}
show "PROP ?ob'83"

(* BEGIN ZENON INPUT
;; file=.tlacache/PetersonLemmas.tlaps/tlapm_f2b980.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/PetersonLemmas.tlaps/tlapm_f2b980.znn.out
;; obligation #83
$hyp "v'32" a_STATEunde_Invunde_a
$hyp "v'33" (a_ACTIONunde_ProcessRequestFlagunde_a 0)
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a (TLA.set 0 (TLA.fapply TLA.Succ 0)))
$hyp "a_CONSTANTunde_qunde_a_in" (TLA.in a_CONSTANTunde_qunde_a (TLA.set 0 (TLA.fapply TLA.Succ 0)))
$hyp "v'47" (=> (/\ (-. (= a_CONSTANTunde_punde_a a_CONSTANTunde_qunde_a))
(= (TLA.fapply a_VARIABLEunde_processStateunde_hash_primea a_CONSTANTunde_punde_a)
"sentRequest")) (= (TLA.fapply a_VARIABLEunde_flagunde_hash_primea a_CONSTANTunde_punde_a)
T.))
$goal (=> (/\ (-. (= a_CONSTANTunde_punde_a a_CONSTANTunde_qunde_a))
(= (TLA.fapply a_VARIABLEunde_processStateunde_hash_primea a_CONSTANTunde_punde_a)
"sentRequest"))
(= (TLA.fapply a_VARIABLEunde_flagunde_hash_primea a_CONSTANTunde_punde_a)
T.))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_He:"(((a_CONSTANTunde_punde_a~=a_CONSTANTunde_qunde_a)&((a_VARIABLEunde_processStateunde_hash_primea[a_CONSTANTunde_punde_a])=''sentRequest''))=>((a_VARIABLEunde_flagunde_hash_primea[a_CONSTANTunde_punde_a])=TRUE))" (is "?z_hg=>?z_ho")
 using v'47 by blast
 assume z_Hf:"(~(?z_hg=>?z_ho))"
 show FALSE
 by (rule notE [OF z_Hf z_He])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 83"; *} qed
lemma ob'111:
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_VARIABLEunde_turnunde_a a_VARIABLEunde_turnunde_a'
fixes a_VARIABLEunde_processStateunde_a a_VARIABLEunde_processStateunde_a'
fixes a_VARIABLEunde_flagunde_a a_VARIABLEunde_flagunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_ProcessRequestFlag_ suppressed *)
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
(* usable definition STATE_critReqs_ suppressed *)
(* usable definition STATE_requestReqs_ suppressed *)
(* usable definition STATE_I_ suppressed *)
(* usable definition STATE_Inv_ suppressed *)
(* usable definition TEMPORAL_MutExSpec_ suppressed *)
(* usable definition TEMPORAL_TestSpec_ suppressed *)
(* usable definition STATE_InvImpMutEx_ suppressed *)
assumes v'32: "(a_STATEunde_Invunde_a)"
assumes v'33: "((a_ACTIONunde_ProcessRequestFlagunde_a (((0)))))"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> ({((0)), ((Succ[0]))}))"
fixes a_CONSTANTunde_qunde_a
assumes a_CONSTANTunde_qunde_a_in : "(a_CONSTANTunde_qunde_a \<in> ({((0)), ((Succ[0]))}))"
assumes v'48: "(((((((a_CONSTANTunde_punde_a) \<noteq> (a_CONSTANTunde_qunde_a))) \<and> (((fapply (((a_VARIABLEunde_processStateunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = (''waiting''))))) \<Longrightarrow> (((fapply (((a_VARIABLEunde_flagunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = (TRUE)))))"
shows "(((((((a_CONSTANTunde_punde_a) \<noteq> (a_CONSTANTunde_qunde_a))) \<and> (((fapply (((a_VARIABLEunde_processStateunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = (''waiting''))))) \<Rightarrow> (((fapply (((a_VARIABLEunde_flagunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = (TRUE)))))"(is "PROP ?ob'111")
proof -
ML_command {* writeln "*** TLAPS ENTER 111"; *}
show "PROP ?ob'111"

(* BEGIN ZENON INPUT
;; file=.tlacache/PetersonLemmas.tlaps/tlapm_b68375.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/PetersonLemmas.tlaps/tlapm_b68375.znn.out
;; obligation #111
$hyp "v'32" a_STATEunde_Invunde_a
$hyp "v'33" (a_ACTIONunde_ProcessRequestFlagunde_a 0)
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a (TLA.set 0 (TLA.fapply TLA.Succ 0)))
$hyp "a_CONSTANTunde_qunde_a_in" (TLA.in a_CONSTANTunde_qunde_a (TLA.set 0 (TLA.fapply TLA.Succ 0)))
$hyp "v'48" (=> (/\ (-. (= a_CONSTANTunde_punde_a a_CONSTANTunde_qunde_a))
(= (TLA.fapply a_VARIABLEunde_processStateunde_hash_primea a_CONSTANTunde_punde_a)
"waiting")) (= (TLA.fapply a_VARIABLEunde_flagunde_hash_primea a_CONSTANTunde_punde_a)
T.))
$goal (=> (/\ (-. (= a_CONSTANTunde_punde_a a_CONSTANTunde_qunde_a))
(= (TLA.fapply a_VARIABLEunde_processStateunde_hash_primea a_CONSTANTunde_punde_a)
"waiting"))
(= (TLA.fapply a_VARIABLEunde_flagunde_hash_primea a_CONSTANTunde_punde_a)
T.))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_He:"(((a_CONSTANTunde_punde_a~=a_CONSTANTunde_qunde_a)&((a_VARIABLEunde_processStateunde_hash_primea[a_CONSTANTunde_punde_a])=''waiting''))=>((a_VARIABLEunde_flagunde_hash_primea[a_CONSTANTunde_punde_a])=TRUE))" (is "?z_hg=>?z_ho")
 using v'48 by blast
 assume z_Hf:"(~(?z_hg=>?z_ho))"
 show FALSE
 by (rule notE [OF z_Hf z_He])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 111"; *} qed
end
