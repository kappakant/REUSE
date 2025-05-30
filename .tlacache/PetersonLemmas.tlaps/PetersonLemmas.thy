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

lemma ob'1:
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
(* usable definition STATE_I_ suppressed *)
(* usable definition STATE_Inv_ suppressed *)
assumes v'26: "(a_STATEunde_Invunde_a)"
assumes v'27: "(a_ACTIONunde_Nextunde_a)"
assumes v'28: "((a_ACTIONunde_ProcessRequestFlagunde_a (((0)))))"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> ({((0)), ((Succ[0]))}))"
fixes a_CONSTANTunde_qunde_a
assumes a_CONSTANTunde_qunde_a_in : "(a_CONSTANTunde_qunde_a \<in> ({((0)), ((Succ[0]))}))"
assumes v'42: "(((a_CONSTANTunde_punde_a) \<noteq> (a_CONSTANTunde_qunde_a)))"
assumes v'43: "(((fapply (((a_VARIABLEunde_processStateunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = (''critical'')))"
assumes v'52: "(((((((fapply (((a_VARIABLEunde_flagunde_hash_primea :: c)), (a_CONSTANTunde_qunde_a))) \<noteq> (FALSE))) \<and> ((((a_VARIABLEunde_turnunde_hash_primea :: c)) \<noteq> (a_CONSTANTunde_punde_a))))) \<and> (((fapply (((a_VARIABLEunde_processStateunde_hash_primea :: c)), (a_CONSTANTunde_qunde_a))) \<noteq> (''sentRequest'')))))"
assumes v'53: "(((((a_VARIABLEunde_turnunde_hash_primea :: c)) \<in> ({((0)), ((Succ[0]))}))) & ((((a_VARIABLEunde_flagunde_hash_primea :: c)) \<in> ([({((0)), ((Succ[0]))}) \<rightarrow> ({(TRUE), (FALSE)})]))) & ((((a_VARIABLEunde_processStateunde_hash_primea :: c)) \<in> ([({((0)), ((Succ[0]))}) \<rightarrow> ({(''idle''), (''sentRequest''), (''waiting''), (''critical'')})]))))"
shows "(((((fapply (((a_VARIABLEunde_flagunde_hash_primea :: c)), (a_CONSTANTunde_qunde_a))) = (TRUE))) \<and> ((((a_VARIABLEunde_turnunde_hash_primea :: c)) = (a_CONSTANTunde_qunde_a)))))"(is "PROP ?ob'1")
proof -
ML_command {* writeln "*** TLAPS ENTER 1"; *}
show "PROP ?ob'1"

(* BEGIN ZENON INPUT
;; file=.tlacache/PetersonLemmas.tlaps/tlapm_192f45.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/PetersonLemmas.tlaps/tlapm_192f45.znn.out
;; obligation #1
$hyp "v'26" a_STATEunde_Invunde_a
$hyp "v'27" a_ACTIONunde_Nextunde_a
$hyp "v'28" (a_ACTIONunde_ProcessRequestFlagunde_a 0)
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a (TLA.set 0 (TLA.fapply TLA.Succ 0)))
$hyp "a_CONSTANTunde_qunde_a_in" (TLA.in a_CONSTANTunde_qunde_a (TLA.set 0 (TLA.fapply TLA.Succ 0)))
$hyp "v'42" (-. (= a_CONSTANTunde_punde_a
a_CONSTANTunde_qunde_a))
$hyp "v'43" (= (TLA.fapply a_VARIABLEunde_processStateunde_hash_primea a_CONSTANTunde_punde_a)
"critical")
$hyp "v'52" (/\ (/\ (-. (= (TLA.fapply a_VARIABLEunde_flagunde_hash_primea a_CONSTANTunde_qunde_a)
F.)) (-. (= a_VARIABLEunde_turnunde_hash_primea a_CONSTANTunde_punde_a)))
(-. (= (TLA.fapply a_VARIABLEunde_processStateunde_hash_primea a_CONSTANTunde_qunde_a)
"sentRequest")))
$hyp "v'53" (/\ (TLA.in a_VARIABLEunde_turnunde_hash_primea
(TLA.set 0 (TLA.fapply TLA.Succ 0)))
(TLA.in a_VARIABLEunde_flagunde_hash_primea
(TLA.FuncSet (TLA.set 0 (TLA.fapply TLA.Succ 0)) (TLA.set T. F.)))
(TLA.in a_VARIABLEunde_processStateunde_hash_primea
(TLA.FuncSet (TLA.set 0 (TLA.fapply TLA.Succ 0)) (TLA.set "idle" "sentRequest" "waiting" "critical"))))
$goal (/\ (= (TLA.fapply a_VARIABLEunde_flagunde_hash_primea a_CONSTANTunde_qunde_a)
T.) (= a_VARIABLEunde_turnunde_hash_primea
a_CONSTANTunde_qunde_a))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hh:"((((a_VARIABLEunde_flagunde_hash_primea[a_CONSTANTunde_qunde_a])~=FALSE)&(a_VARIABLEunde_turnunde_hash_primea~=a_CONSTANTunde_punde_a))&((a_VARIABLEunde_processStateunde_hash_primea[a_CONSTANTunde_qunde_a])~=''sentRequest''))" (is "?z_hk&?z_ht")
 using v'52 by blast
 have z_Hi:"((a_VARIABLEunde_turnunde_hash_primea \\in {0, 1})&((a_VARIABLEunde_flagunde_hash_primea \\in FuncSet({0, 1}, {TRUE, FALSE}))&(a_VARIABLEunde_processStateunde_hash_primea \\in FuncSet({0, 1}, {''idle'', ''sentRequest'', ''waiting'', ''critical''}))))" (is "?z_hx&?z_hbb")
 using v'53 by blast
 have z_He:"(a_CONSTANTunde_qunde_a \\in {0, 1})" (is "?z_he")
 using a_CONSTANTunde_qunde_a_in by blast
 have z_Hf:"(a_CONSTANTunde_punde_a~=a_CONSTANTunde_qunde_a)"
 using v'42 by blast
 have z_Hd:"(a_CONSTANTunde_punde_a \\in {0, 1})" (is "?z_hd")
 using a_CONSTANTunde_punde_a_in by blast
 assume z_Hj:"(~(((a_VARIABLEunde_flagunde_hash_primea[a_CONSTANTunde_qunde_a])=TRUE)&(a_VARIABLEunde_turnunde_hash_primea=a_CONSTANTunde_qunde_a)))" (is "~(?z_hbn&?z_hbo)")
 have z_Hk: "?z_hk" (is "?z_hl&?z_hq")
 by (rule zenon_and_0 [OF z_Hh])
 have z_Hl: "?z_hl" (is "?z_hm~=?z_hp")
 by (rule zenon_and_0 [OF z_Hk])
 have z_Hq: "?z_hq"
 by (rule zenon_and_1 [OF z_Hk])
 have z_Hx: "?z_hx"
 by (rule zenon_and_0 [OF z_Hi])
 have z_Hbb: "?z_hbb" (is "?z_hbc&?z_hbg")
 by (rule zenon_and_1 [OF z_Hi])
 have z_Hbc: "?z_hbc"
 by (rule zenon_and_0 [OF z_Hbb])
 show FALSE
 proof (rule zenon_in_addElt [of "a_VARIABLEunde_turnunde_hash_primea" "0" "{1}", OF z_Hx])
  assume z_Hbq:"(a_VARIABLEunde_turnunde_hash_primea=0)"
  show FALSE
  proof (rule zenon_in_addElt [of "a_CONSTANTunde_punde_a" "0" "{1}", OF z_Hd])
   assume z_Hbr:"(a_CONSTANTunde_punde_a=0)"
   show FALSE
   proof (rule notE [OF z_Hq])
    have z_Hbs: "(0=a_CONSTANTunde_punde_a)"
    by (rule sym [OF z_Hbr])
    have z_Hbt: "(a_VARIABLEunde_turnunde_hash_primea=a_CONSTANTunde_punde_a)"
    by (rule subst [where P="(\<lambda>zenon_Vjo. (a_VARIABLEunde_turnunde_hash_primea=zenon_Vjo))", OF z_Hbs], fact z_Hbq)
    thus "(a_VARIABLEunde_turnunde_hash_primea=a_CONSTANTunde_punde_a)" .
   qed
  next
   assume z_Hbx:"(a_CONSTANTunde_punde_a \\in {1})" (is "?z_hbx")
   show FALSE
   proof (rule zenon_in_addElt [of "a_CONSTANTunde_punde_a" "1" "{}", OF z_Hbx])
    assume z_Hbz:"(a_CONSTANTunde_punde_a=1)" (is "_=?z_hba")
    show FALSE
    proof (rule zenon_in_addElt [of "a_CONSTANTunde_qunde_a" "0" "{?z_hba}", OF z_He])
     assume z_Hca:"(a_CONSTANTunde_qunde_a=0)"
     show FALSE
     proof (rule zenon_notand [OF z_Hj])
      assume z_Hcb:"(?z_hm~=TRUE)" (is "_~=?z_hbf")
      have z_Hcc: "(~?z_hm)"
      by (rule zenon_noteq_x_true_0 [of "?z_hm", OF z_Hcb])
      have z_Hcd: "(\\A zenon_Vz:((zenon_Vz \\in {0, ?z_hba})=>((a_VARIABLEunde_flagunde_hash_primea[zenon_Vz]) \\in {?z_hbf, ?z_hp})))" (is "\\A x : ?z_hcj(x)")
      by (rule zenon_in_funcset_2 [of "a_VARIABLEunde_flagunde_hash_primea" "{0, ?z_hba}" "{?z_hbf, ?z_hp}", OF z_Hbc])
      have z_Hck: "?z_hcj(0)" (is "?z_hcl=>?z_hcm")
      by (rule zenon_all_0 [of "?z_hcj" "0", OF z_Hcd])
      show FALSE
      proof (rule zenon_imply [OF z_Hck])
       assume z_Hcn:"(~?z_hcl)"
       have z_Hco: "(0~=0)"
       by (rule zenon_notin_addElt_0 [of "0" "0" "{?z_hba}", OF z_Hcn])
       show FALSE
       by (rule zenon_noteq [OF z_Hco])
      next
       assume z_Hcm:"?z_hcm"
       show FALSE
       proof (rule zenon_in_addElt [of "(a_VARIABLEunde_flagunde_hash_primea[0])" "?z_hbf" "{?z_hp}", OF z_Hcm])
        assume z_Hcr:"((a_VARIABLEunde_flagunde_hash_primea[0])=?z_hbf)" (is "?z_hcp=_")
        have z_Hcp: "?z_hcp"
        by (rule zenon_eq_x_true_0 [of "?z_hcp", OF z_Hcr])
        show FALSE
        proof (rule notE [OF z_Hcc])
         have z_Hcs: "(0=a_CONSTANTunde_qunde_a)"
         by (rule sym [OF z_Hca])
         have z_Hm: "?z_hm"
         by (rule subst [where P="(\<lambda>zenon_Vpm. (a_VARIABLEunde_flagunde_hash_primea[zenon_Vpm]))", OF z_Hcs], fact z_Hcp)
         thus "?z_hm" .
        qed
       next
        assume z_Hcw:"((a_VARIABLEunde_flagunde_hash_primea[0]) \\in {?z_hp})" (is "?z_hcw")
        show FALSE
        proof (rule zenon_in_addElt [of "(a_VARIABLEunde_flagunde_hash_primea[0])" "?z_hp" "{}", OF z_Hcw])
         assume z_Hcx:"((a_VARIABLEunde_flagunde_hash_primea[0])=?z_hp)" (is "?z_hcp=_")
         show FALSE
         proof (rule notE [OF z_Hl])
          have z_Hcy: "(?z_hcp=?z_hm)"
          proof (rule zenon_nnpp [of "(?z_hcp=?z_hm)"])
           assume z_Hcz:"(?z_hcp~=?z_hm)"
           show FALSE
           proof (rule zenon_em [of "(?z_hm=?z_hm)"])
            assume z_Hda:"(?z_hm=?z_hm)"
            show FALSE
            proof (rule notE [OF z_Hcz])
             have z_Hdb: "(?z_hm=?z_hcp)"
             proof (rule zenon_nnpp [of "(?z_hm=?z_hcp)"])
              assume z_Hdc:"(?z_hm~=?z_hcp)"
              show FALSE
              proof (rule zenon_noteq [of "?z_hcp"])
               have z_Hdd: "(?z_hcp~=?z_hcp)"
               by (rule subst [where P="(\<lambda>zenon_Vmm. ((a_VARIABLEunde_flagunde_hash_primea[zenon_Vmm])~=?z_hcp))", OF z_Hca], fact z_Hdc)
               thus "(?z_hcp~=?z_hcp)" .
              qed
             qed
             have z_Hcy: "(?z_hcp=?z_hm)"
             by (rule subst [where P="(\<lambda>zenon_Vmo. (zenon_Vmo=?z_hm))", OF z_Hdb], fact z_Hda)
             thus "(?z_hcp=?z_hm)" .
            qed
           next
            assume z_Hdl:"(?z_hm~=?z_hm)"
            show FALSE
            by (rule zenon_noteq [OF z_Hdl])
           qed
          qed
          have z_Hdm: "(?z_hm=?z_hp)"
          by (rule subst [where P="(\<lambda>zenon_Vno. (zenon_Vno=?z_hp))", OF z_Hcy], fact z_Hcx)
          thus "(?z_hm=?z_hp)" .
         qed
        next
         assume z_Hdq:"((a_VARIABLEunde_flagunde_hash_primea[0]) \\in {})" (is "?z_hdq")
         show FALSE
         by (rule zenon_in_emptyset [of "(a_VARIABLEunde_flagunde_hash_primea[0])", OF z_Hdq])
        qed
       qed
      qed
     next
      assume z_Hdr:"(a_VARIABLEunde_turnunde_hash_primea~=a_CONSTANTunde_qunde_a)"
      show FALSE
      proof (rule notE [OF z_Hdr])
       have z_Hcs: "(0=a_CONSTANTunde_qunde_a)"
       by (rule sym [OF z_Hca])
       have z_Hbo: "?z_hbo"
       by (rule subst [where P="(\<lambda>zenon_Vjo. (a_VARIABLEunde_turnunde_hash_primea=zenon_Vjo))", OF z_Hcs], fact z_Hbq)
       thus "?z_hbo" .
      qed
     qed
    next
     assume z_Hds:"(a_CONSTANTunde_qunde_a \\in {?z_hba})" (is "?z_hds")
     show FALSE
     proof (rule zenon_in_addElt [of "a_CONSTANTunde_qunde_a" "?z_hba" "{}", OF z_Hds])
      assume z_Hdt:"(a_CONSTANTunde_qunde_a=?z_hba)"
      show FALSE
      proof (rule zenon_em [of "(a_CONSTANTunde_qunde_a=a_CONSTANTunde_qunde_a)"])
       assume z_Hdu:"(a_CONSTANTunde_qunde_a=a_CONSTANTunde_qunde_a)"
       show FALSE
       proof (rule notE [OF z_Hf])
        have z_Hdv: "(a_CONSTANTunde_qunde_a=a_CONSTANTunde_punde_a)"
        proof (rule zenon_nnpp [of "(a_CONSTANTunde_qunde_a=a_CONSTANTunde_punde_a)"])
         assume z_Hdw:"(a_CONSTANTunde_qunde_a~=a_CONSTANTunde_punde_a)"
         show FALSE
         proof (rule notE [OF z_Hdw])
          have z_Hdx: "(?z_hba=a_CONSTANTunde_punde_a)"
          by (rule sym [OF z_Hbz])
          have z_Hdv: "(a_CONSTANTunde_qunde_a=a_CONSTANTunde_punde_a)"
          by (rule subst [where P="(\<lambda>zenon_Vvn. (a_CONSTANTunde_qunde_a=zenon_Vvn))", OF z_Hdx], fact z_Hdt)
          thus "(a_CONSTANTunde_qunde_a=a_CONSTANTunde_punde_a)" .
         qed
        qed
        have z_Heb: "(a_CONSTANTunde_punde_a=a_CONSTANTunde_qunde_a)"
        by (rule subst [where P="(\<lambda>zenon_Vqo. (zenon_Vqo=a_CONSTANTunde_qunde_a))", OF z_Hdv], fact z_Hdu)
        thus "(a_CONSTANTunde_punde_a=a_CONSTANTunde_qunde_a)" .
       qed
      next
       assume z_Hef:"(a_CONSTANTunde_qunde_a~=a_CONSTANTunde_qunde_a)"
       show FALSE
       by (rule zenon_noteq [OF z_Hef])
      qed
     next
      assume z_Heg:"(a_CONSTANTunde_qunde_a \\in {})" (is "?z_heg")
      show FALSE
      by (rule zenon_in_emptyset [of "a_CONSTANTunde_qunde_a", OF z_Heg])
     qed
    qed
   next
    assume z_Heh:"(a_CONSTANTunde_punde_a \\in {})" (is "?z_heh")
    show FALSE
    by (rule zenon_in_emptyset [of "a_CONSTANTunde_punde_a", OF z_Heh])
   qed
  qed
 next
  assume z_Hei:"(a_VARIABLEunde_turnunde_hash_primea \\in {1})" (is "?z_hei")
  show FALSE
  proof (rule zenon_in_addElt [of "a_VARIABLEunde_turnunde_hash_primea" "1" "{}", OF z_Hei])
   assume z_Hej:"(a_VARIABLEunde_turnunde_hash_primea=1)" (is "_=?z_hba")
   show FALSE
   proof (rule zenon_in_addElt [of "a_CONSTANTunde_punde_a" "0" "{?z_hba}", OF z_Hd])
    assume z_Hbr:"(a_CONSTANTunde_punde_a=0)"
    show FALSE
    proof (rule zenon_in_addElt [of "a_CONSTANTunde_qunde_a" "0" "{?z_hba}", OF z_He])
     assume z_Hca:"(a_CONSTANTunde_qunde_a=0)"
     show FALSE
     proof (rule notE [OF z_Hf])
      have z_Hcs: "(0=a_CONSTANTunde_qunde_a)"
      by (rule sym [OF z_Hca])
      have z_Heb: "(a_CONSTANTunde_punde_a=a_CONSTANTunde_qunde_a)"
      by (rule subst [where P="(\<lambda>zenon_Vun. (a_CONSTANTunde_punde_a=zenon_Vun))", OF z_Hcs], fact z_Hbr)
      thus "(a_CONSTANTunde_punde_a=a_CONSTANTunde_qunde_a)" .
     qed
    next
     assume z_Hds:"(a_CONSTANTunde_qunde_a \\in {?z_hba})" (is "?z_hds")
     show FALSE
     proof (rule zenon_in_addElt [of "a_CONSTANTunde_qunde_a" "?z_hba" "{}", OF z_Hds])
      assume z_Hdt:"(a_CONSTANTunde_qunde_a=?z_hba)"
      show FALSE
      proof (rule zenon_notand [OF z_Hj])
       assume z_Hcb:"(?z_hm~=TRUE)" (is "_~=?z_hbf")
       have z_Hcc: "(~?z_hm)"
       by (rule zenon_noteq_x_true_0 [of "?z_hm", OF z_Hcb])
       have z_Hcd: "(\\A zenon_Vz:((zenon_Vz \\in {0, ?z_hba})=>((a_VARIABLEunde_flagunde_hash_primea[zenon_Vz]) \\in {?z_hbf, ?z_hp})))" (is "\\A x : ?z_hcj(x)")
       by (rule zenon_in_funcset_2 [of "a_VARIABLEunde_flagunde_hash_primea" "{0, ?z_hba}" "{?z_hbf, ?z_hp}", OF z_Hbc])
       have z_Hen: "?z_hcj(?z_hba)" (is "?z_heo=>?z_hep")
       by (rule zenon_all_0 [of "?z_hcj" "?z_hba", OF z_Hcd])
       show FALSE
       proof (rule zenon_imply [OF z_Hen])
        assume z_Heq:"(~?z_heo)"
        have z_Her: "(~(?z_hba \\in {?z_hba}))" (is "~?z_hes")
        by (rule zenon_notin_addElt_1 [of "?z_hba" "0" "{?z_hba}", OF z_Heq])
        have z_Het: "(?z_hba~=?z_hba)"
        by (rule zenon_notin_addElt_0 [of "?z_hba" "?z_hba" "{}", OF z_Her])
        show FALSE
        by (rule zenon_noteq [OF z_Het])
       next
        assume z_Hep:"?z_hep"
        show FALSE
        proof (rule zenon_in_addElt [of "(a_VARIABLEunde_flagunde_hash_primea[?z_hba])" "?z_hbf" "{?z_hp}", OF z_Hep])
         assume z_Hev:"((a_VARIABLEunde_flagunde_hash_primea[?z_hba])=?z_hbf)" (is "?z_heu=_")
         have z_Heu: "?z_heu"
         by (rule zenon_eq_x_true_0 [of "?z_heu", OF z_Hev])
         show FALSE
         proof (rule notE [OF z_Hcc])
          have z_Hew: "(?z_hba=a_CONSTANTunde_qunde_a)"
          by (rule sym [OF z_Hdt])
          have z_Hm: "?z_hm"
          by (rule subst [where P="(\<lambda>zenon_Vpm. (a_VARIABLEunde_flagunde_hash_primea[zenon_Vpm]))", OF z_Hew], fact z_Heu)
          thus "?z_hm" .
         qed
        next
         assume z_Hex:"((a_VARIABLEunde_flagunde_hash_primea[?z_hba]) \\in {?z_hp})" (is "?z_hex")
         show FALSE
         proof (rule zenon_in_addElt [of "(a_VARIABLEunde_flagunde_hash_primea[?z_hba])" "?z_hp" "{}", OF z_Hex])
          assume z_Hey:"((a_VARIABLEunde_flagunde_hash_primea[?z_hba])=?z_hp)" (is "?z_heu=_")
          show FALSE
          proof (rule notE [OF z_Hl])
           have z_Hez: "(?z_heu=?z_hm)"
           proof (rule zenon_nnpp [of "(?z_heu=?z_hm)"])
            assume z_Hfa:"(?z_heu~=?z_hm)"
            show FALSE
            proof (rule zenon_em [of "(?z_hm=?z_hm)"])
             assume z_Hda:"(?z_hm=?z_hm)"
             show FALSE
             proof (rule notE [OF z_Hfa])
              have z_Hfb: "(?z_hm=?z_heu)"
              proof (rule zenon_nnpp [of "(?z_hm=?z_heu)"])
               assume z_Hfc:"(?z_hm~=?z_heu)"
               show FALSE
               proof (rule zenon_noteq [of "?z_heu"])
               have z_Hfd: "(?z_heu~=?z_heu)"
               by (rule subst [where P="(\<lambda>zenon_Vgm. ((a_VARIABLEunde_flagunde_hash_primea[zenon_Vgm])~=?z_heu))", OF z_Hdt], fact z_Hfc)
               thus "(?z_heu~=?z_heu)" .
               qed
              qed
              have z_Hez: "(?z_heu=?z_hm)"
              by (rule subst [where P="(\<lambda>zenon_Vmo. (zenon_Vmo=?z_hm))", OF z_Hfb], fact z_Hda)
              thus "(?z_heu=?z_hm)" .
             qed
            next
             assume z_Hdl:"(?z_hm~=?z_hm)"
             show FALSE
             by (rule zenon_noteq [OF z_Hdl])
            qed
           qed
           have z_Hdm: "(?z_hm=?z_hp)"
           by (rule subst [where P="(\<lambda>zenon_Vno. (zenon_Vno=?z_hp))", OF z_Hez], fact z_Hey)
           thus "(?z_hm=?z_hp)" .
          qed
         next
          assume z_Hfi:"((a_VARIABLEunde_flagunde_hash_primea[?z_hba]) \\in {})" (is "?z_hfi")
          show FALSE
          by (rule zenon_in_emptyset [of "(a_VARIABLEunde_flagunde_hash_primea[?z_hba])", OF z_Hfi])
         qed
        qed
       qed
      next
       assume z_Hdr:"(a_VARIABLEunde_turnunde_hash_primea~=a_CONSTANTunde_qunde_a)"
       show FALSE
       proof (rule notE [OF z_Hdr])
        have z_Hew: "(?z_hba=a_CONSTANTunde_qunde_a)"
        by (rule sym [OF z_Hdt])
        have z_Hbo: "?z_hbo"
        by (rule subst [where P="(\<lambda>zenon_Vjo. (a_VARIABLEunde_turnunde_hash_primea=zenon_Vjo))", OF z_Hew], fact z_Hej)
        thus "?z_hbo" .
       qed
      qed
     next
      assume z_Heg:"(a_CONSTANTunde_qunde_a \\in {})" (is "?z_heg")
      show FALSE
      by (rule zenon_in_emptyset [of "a_CONSTANTunde_qunde_a", OF z_Heg])
     qed
    qed
   next
    assume z_Hbx:"(a_CONSTANTunde_punde_a \\in {?z_hba})" (is "?z_hbx")
    show FALSE
    proof (rule zenon_in_addElt [of "a_CONSTANTunde_punde_a" "?z_hba" "{}", OF z_Hbx])
     assume z_Hbz:"(a_CONSTANTunde_punde_a=?z_hba)"
     show FALSE
     proof (rule notE [OF z_Hq])
      have z_Hdx: "(?z_hba=a_CONSTANTunde_punde_a)"
      by (rule sym [OF z_Hbz])
      have z_Hbt: "(a_VARIABLEunde_turnunde_hash_primea=a_CONSTANTunde_punde_a)"
      by (rule subst [where P="(\<lambda>zenon_Vjo. (a_VARIABLEunde_turnunde_hash_primea=zenon_Vjo))", OF z_Hdx], fact z_Hej)
      thus "(a_VARIABLEunde_turnunde_hash_primea=a_CONSTANTunde_punde_a)" .
     qed
    next
     assume z_Heh:"(a_CONSTANTunde_punde_a \\in {})" (is "?z_heh")
     show FALSE
     by (rule zenon_in_emptyset [of "a_CONSTANTunde_punde_a", OF z_Heh])
    qed
   qed
  next
   assume z_Hfj:"(a_VARIABLEunde_turnunde_hash_primea \\in {})" (is "?z_hfj")
   show FALSE
   by (rule zenon_in_emptyset [of "a_VARIABLEunde_turnunde_hash_primea", OF z_Hfj])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1"; *} qed
end
