theory Refine_AC_A
imports
  TPM_Corres
begin

definition trusted_boot :: "nat \<Rightarrow> unit E_monad"
  where "trusted_boot (i::nat) \<equiv> doE
      sealed_pp \<leftarrow> (read_passphrase i);
      pp_auth \<leftarrow> get_authdata;
      srk_auth \<leftarrow> get_authdata;
      passphrase \<leftarrow> unseal_passphrase srk_auth pp_auth sealed_pp;
      returnOk ()
    odE"
       
context sable_m
begin

section {* Correspondence Example *}
  
text {* In this lemma, we establish that our lifted C implementation of
\texttt{read\_passphrase()} corresponds to the same definition in our abstract
specification. The \texttt{read\_passphrase()} reads the configuration pass
phrase from the TPM chip's NVRAM, and returns it as an unpacked structured of
type \texttt{TPM\_STORED\_DATA12}, according to the TCG standard. The abstract
function is very simple. It simply calls the abstract TPM driver function
\textsf{TPM\_NV\_ReadValue} and returns. The C implementation is more complex. It also
calls the C implementation \texttt{TPM\_NV\_ReadValue()}, but it then must verify
that the call to the driver succeeded and, if so, unpack the retrieved data
structure containing the passphrase. *}
  
lemma read_passphrase_corres:
  "corres (R_STORED_DATA_rel string_rel) \<top> \<top> (read_passphrase i)
                                              (read_passphrase' (of_nat i))"
  (is "corres ?r _ _ _ _")
unfolding read_passphrase_def read_passphrase'_def
proof simp
  let ?r' = "R_HEAP_DATA_rel (E_STORED_DATA_rel string_rel)"
  show "corres ?r \<top> \<top> 
       (* Abstract read_passphrase *)
       (TPM_NV_ReadValue i 0 None)
       (* AutoCorres lifted read_passphrase() *)
       (do ret' \<leftarrow> TPM_NV_ReadValue' (of_nat i) 0 0x190
               (TPM_AUTHDATA_option_C
                  (tdTPM_AUTHDATA_C (ARRAY _. 0)) 0) NULL;
         condition
           (\<lambda>s. error_C (HEAP_DATA_exception_C.exception_C ret') \<noteq> 0)
           (return (TPM_STORED_DATA12_exception_C
                (HEAP_DATA_exception_C.exception_C ret')
              (tdTPM_STORED_DATA12_C 0 0 0 NULL 0 NULL)))
           (do ret' \<leftarrow>
               unpack_TPM_STORED_DATA12' (tdHEAP_DATA_C.data_C 
                      (HEAP_DATA_exception_C.value_C ret'))
                (tdHEAP_DATA_C.dataSize_C
                   (HEAP_DATA_exception_C.value_C ret'));
               return (TPM_STORED_DATA12_exception_C
                         (tdEXCEPTION_C NONE) ret')
            od)
      od)" (is "corres ?r _ _ ?read (?read' >>= ?d)")
  apply (rule corres_bind_return)
  apply (rule corres_guard_imp [where Q="\<top> and \<top>" and Q'="\<top> and \<top>"])
  apply (rule corres_split [where r'="?r'" and R="\<top>\<top>" and R'="\<top>\<top>"])
  proof simp_all
    fix rv rv'
    show "corres ?r \<top> (\<lambda>s'. ?r' rv (rv', s')) (return rv) (?d rv')"
      (is "corres _ _ _ _ (condition (?c rv') (?t rv') (?f rv'))")
    apply (rule corres_assume_pre, simp)
    proof (cases rv)
      case (Inl e)
      fix s'
      assume "?r' rv (rv', s')"
      with Inl have
        rv': "error_C (HEAP_DATA_exception_C.exception_C rv') \<noteq> NONE"
        unfolding R_HEAP_DATA_rel_def ERROR_rel_def by simp
      hence "?c rv' s'" by (simp add: NONE_def)
      from Inl and rv' have
        "corres ?r \<top> (\<lambda>s'. ?r' rv (rv', s')) (return rv) (?t rv')"
        by (simp add: R_HEAP_DATA_rel_def R_STORED_DATA_rel_def)
      thus ?thesis using `?c rv' s'` by auto
    next
      let ?error = "error_C (HEAP_DATA_exception_C.exception_C rv')"
      let ?data =
        "tdHEAP_DATA_C.data_C (HEAP_DATA_exception_C.value_C rv')"
      let ?dataSize = "tdHEAP_DATA_C.dataSize_C
                         (HEAP_DATA_exception_C.value_C rv')"
      case (Inr v)
      fix s'
      assume "?r' rv (rv', s')"
      with Inr have rv'_e: "?error = NONE"
        unfolding R_HEAP_DATA_rel_def ERROR_rel_def by simp
      hence "\<not>?c rv' s'" by (simp add: NONE_def)
      from Inr and `?r' rv (rv', s')` have rv'_v:
        "HEAP_DATA_rel (E_STORED_DATA_rel string_rel) v
           (HEAP_DATA_exception_C.value_C rv', s')"
        unfolding R_HEAP_DATA_rel_def by simp
      hence unpack: "\<forall>r \<in> fst (unpack_TPM_STORED_DATA12' ?data ?dataSize s').
          STORED_DATA_rel string_rel v r"
        unfolding HEAP_DATA_rel_def E_STORED_DATA_rel_def by simp
      let ?r'' =
        "\<lambda>rv rv'. case rv of Inl e \<Rightarrow> False
                           | Inr v \<Rightarrow> STORED_DATA_rel string_rel v rv'"
      let ?unpack = "unpack_TPM_STORED_DATA12' ?data ?dataSize"
      have "corres ?r \<top> (\<lambda>s'. ?r' (Inr v) (rv', s')) (return (Inr v)) (?f rv')"
      apply (rule corres_bind_return)
      proof (rule corres_split' [where r'="?r''" and Q="\<top>\<top>" and Q'="\<top>\<top>"])
        have p: "\<forall>(s, s') \<in> SR. ?r' (Inr v) (rv', s')
                 \<longrightarrow> (\<forall>(r', t') \<in> fst (?unpack s').
             \<exists>(r, t) \<in> fst (return (Inr v) s). (t, t') \<in> SR \<and> ?r'' r (r', t'))"
          unfolding R_HEAP_DATA_rel_def STORED_DATA_rel_def return_def by simp
        with no_fail_unpack_TPM_STORED_DATA12'
        show "corres ?r'' \<top> (\<lambda>s'. ?r' (Inr v) (rv', s'))
                (return (Inr v)) ?unpack"
          by (fast intro!: corres_no_failI)
      next
        show "\<And>rv rv'. corres ?r \<top> (\<lambda>s'. ?r'' rv (rv', s') \<and> True) (return rv)
          (return (TPM_STORED_DATA12_exception_C (tdEXCEPTION_C NONE) rv'))"
          by (case_tac rv,
              auto simp add: R_STORED_DATA_rel_def STORED_DATA_rel_def)
      next show "\<lbrace>\<top>\<rbrace> return (Inr v) \<lbrace>\<top>\<top>\<rbrace>" by (rule hoare_post_taut)
      next show "\<lbrace>\<lambda>s'. ?r' (Inr v) (rv', s')\<rbrace> ?unpack \<lbrace>\<top>\<top>\<rbrace>"
          by (rule hoare_post_taut)
      qed
      thus ?thesis using Inr and `\<not>?c rv' s'` by simp
    qed
  next show "corres ?r' \<top> \<top> ?read ?read'" using TPM_NV_ReadValue_corres
         by (metis of_nat_numeral semiring_1_class.of_nat_0)
  next show "\<lbrace>\<top>\<rbrace> ?read \<lbrace>\<top>\<top>\<rbrace>" by (rule hoare_post_taut)
  next show"\<lbrace>\<lambda>_. True\<rbrace> ?read' \<lbrace>\<lambda>_ _. True\<rbrace>" by (rule hoare_post_taut)
  qed
qed
        
lemma ERROR_rel_imp_error_not_none_TPM_STORED_DATA12:
  "ERROR_rel x1 (error_C (TPM_STORED_DATA12_exception_C.exception_C rv'))
    \<Longrightarrow> error_C (TPM_STORED_DATA12_exception_C.exception_C rv') \<noteq> NONE"
  unfolding ERROR_rel_def by auto
    
lemma ERROR_rel_imp_error_not_none_TPM_AUTHDATA:
  "ERROR_rel x1 (error_C (TPM_AUTHDATA_exception_C.exception_C rv'))
    \<Longrightarrow> error_C (TPM_AUTHDATA_exception_C.exception_C rv') \<noteq> NONE"
  unfolding ERROR_rel_def by blast
    
lemma ERROR_rel_imp_error_not_none_CSTRING:
  "ERROR_rel x1 (error_C (CSTRING_exception_C.exception_C rv'))
    \<Longrightarrow> error_C (CSTRING_exception_C.exception_C rv') \<noteq> NONE"
  unfolding ERROR_rel_def by blast
        
lemma extract_assms_from_corres:
  "(!s. P s \<longrightarrow> Assm ) \<Longrightarrow> (!s. P' s \<longrightarrow> Assm') \<Longrightarrow> Assm \<and> Assm' \<longrightarrow> corres rrel P P' m m' \<Longrightarrow> 
   corres rrel P P' m m'"
  by (metis corres_req)
    
lemma simp_if_inside_independent_lambda: 
  "(if p then f else g) = (\<lambda> s. if p then f s else g s)" 
  by simp
  
(* convenience lemmas for dealing with exception monad results in correspondence proofs,
  they turned out uglier than I'd hoped*)
lemma simplifyExMonad_TPM_AUTHDATA:"returnExRel_TPM_AUTHDATA rv rv' \<and>
  (\<forall>rvOk. (rv = Inr rvOk \<and> error_C (TPM_AUTHDATA_exception_C.exception_C rv') = 0 \<longrightarrow>
   corres rrel G G' (m rvOk) m')) \<Longrightarrow>
   \<forall> error error' ss'. ERROR_rel error (tdEXCEPTION_C.error_C  error')
    \<longrightarrow>  rrel (Inl error) ((tdRESULT_C error'), ss')  \<Longrightarrow>
  corres rrel G G' 
    (case rv of Inl e \<Rightarrow> throwError e  | Inr v' \<Rightarrow> m v')
    (\<lambda>s. if error_C (TPM_AUTHDATA_exception_C.exception_C rv') \<noteq> 0
             then return (tdRESULT_C.exception_C_update  (\<lambda>a. TPM_AUTHDATA_exception_C.exception_C rv') rv'Base) s 
             else m' s)"
  apply (auto split:sum.split) 
    apply (frule ERROR_rel_imp_error_not_none_TPM_AUTHDATA)
  unfolding NONE_def
proof auto
  fix rrel rv rv' G G' rv'Base
  fix x1 
  assume the_error_rel:"ERROR_rel x1 (error_C (TPM_AUTHDATA_exception_C.exception_C rv'))"
    and error_rel_imp_rrel:"\<forall>error error'.
             ERROR_rel error (error_C error') \<longrightarrow>
             (\<forall>ss'. rrel (Inl error) (tdRESULT_C error', ss'))" 
    and "rv = Inl x1"
  have 0:"tdRESULT_C (TPM_AUTHDATA_exception_C.exception_C rv') = 
          (tdRESULT_C.exception_C_update (\<lambda>a. TPM_AUTHDATA_exception_C.exception_C rv') rv'Base)"
    by (metis tdRESULT_C_accupd_same tdRESULT_C_idupdates(1))
  have "corres_underlying UNIV False True rrel G G' (throwError x1)
           (return (tdRESULT_C (TPM_AUTHDATA_exception_C.exception_C rv')))"
    by (simp add: error_rel_imp_rrel the_error_rel throwError_def) 
  thus "error_C (TPM_AUTHDATA_exception_C.exception_C rv') \<noteq> 0 \<Longrightarrow>
          corres_underlying UNIV False True rrel G G' (throwError x1)
           (return
             (tdRESULT_C.exception_C_update (\<lambda>a. TPM_AUTHDATA_exception_C.exception_C rv') rv'Base))"
    apply (subst 0[THEN sym]) by simp
qed
  
lemma simplifyExMonad_CSTRING:"returnExRel_CSTRING rv rv' \<and>
  (\<forall> rvOk. (rv = Inr rvOk \<and> error_C (CSTRING_exception_C.exception_C rv') = 0 \<longrightarrow>
   corres rrel G G' (m rvOk) m'))\<and>
    (\<forall> error error' ss'. ERROR_rel error (tdEXCEPTION_C.error_C  error')
      \<longrightarrow>  rrel (Inl error) ((tdRESULT_C error'), ss')) \<Longrightarrow>
   \<forall> error error' ss'. ERROR_rel error (tdEXCEPTION_C.error_C  error')
    \<longrightarrow>  rrel (Inl error) ((tdRESULT_C error'), ss')  \<Longrightarrow>
  corres rrel G G' 
    (case rv of Inl e \<Rightarrow> throwError e  | Inr v' \<Rightarrow> m v')
    (\<lambda>s. if error_C (CSTRING_exception_C.exception_C rv') \<noteq> 0
             then return (tdRESULT_C.exception_C_update  (\<lambda>a. CSTRING_exception_C.exception_C rv') rv'Base) s 
             else m' s)"
  apply (auto split:sum.split) 
    apply (frule ERROR_rel_imp_error_not_none_CSTRING)
  unfolding NONE_def
proof auto
  fix rrel rv rv' G G' rv'Base
  fix x1 
  assume the_error_rel:"ERROR_rel x1 (error_C (CSTRING_exception_C.exception_C rv'))"
    and error_rel_imp_rrel:"\<forall>error error'.
             ERROR_rel error (error_C error') \<longrightarrow>
             (\<forall>ss'. rrel (Inl error) (tdRESULT_C error', ss'))" 
    and "rv = Inl x1"
  have 0:"tdRESULT_C (CSTRING_exception_C.exception_C rv') = 
          (tdRESULT_C.exception_C_update (\<lambda>a. CSTRING_exception_C.exception_C rv') rv'Base)"
    by (metis tdRESULT_C_accupd_same tdRESULT_C_idupdates(1))
  have "corres_underlying UNIV False True rrel G G' (throwError x1)
           (return (tdRESULT_C (CSTRING_exception_C.exception_C rv')))"
    by (simp add: error_rel_imp_rrel the_error_rel throwError_def) 
  thus "error_C (CSTRING_exception_C.exception_C rv') \<noteq> 0 \<Longrightarrow>
          corres_underlying UNIV False True rrel G G' (throwError x1)
           (return
             (tdRESULT_C.exception_C_update (\<lambda>a. CSTRING_exception_C.exception_C rv') rv'Base))"
    apply (subst 0[THEN sym]) by simp
qed
  
lemma simplifyExMonad_TPM_STORED_DATA12:"
   returnExRel_TPM_STORED_DATA12 rv rv' \<and>
  (\<forall>rvOk .(rv = Inr rvOk \<longrightarrow> error_C (TPM_STORED_DATA12_exception_C.exception_C rv') = 0 \<longrightarrow>
     corres rrel G G' (m rvOk) m'))  \<and>
    (\<forall> error error' ss'. ERROR_rel error (tdEXCEPTION_C.error_C  error')
      \<longrightarrow>  rrel (Inl error) ((tdRESULT_C error'), ss')) \<Longrightarrow>
  corres rrel G G' 
    (case rv of Inl e \<Rightarrow> throwError e  | Inr rvOk \<Rightarrow> m rvOk)
    (\<lambda>s. if error_C (TPM_STORED_DATA12_exception_C.exception_C rv') \<noteq> 0
             then return (tdRESULT_C.exception_C_update  (\<lambda>a. TPM_STORED_DATA12_exception_C.exception_C rv') rv'Base) s 
             else m' s)"
  apply (auto split:sum.split) 
    apply (frule ERROR_rel_imp_error_not_none_TPM_STORED_DATA12)
  unfolding NONE_def
proof auto
  fix rrel rv rv' G G' rv'Base
  fix x1 
  assume the_error_rel:"ERROR_rel x1 (error_C (TPM_STORED_DATA12_exception_C.exception_C rv'))"    
    and  error_rel_imp_rrel:"\<forall>error error'. ERROR_rel error (error_C error') \<longrightarrow>
          (\<forall>ss'. rrel (Inl error) (tdRESULT_C error', ss'))"       
    and "rv = Inl x1"        
    and "error_C (TPM_STORED_DATA12_exception_C.exception_C rv') \<noteq> 0"
  have 0:"tdRESULT_C (TPM_STORED_DATA12_exception_C.exception_C rv') = 
          (tdRESULT_C.exception_C_update (\<lambda>a. TPM_STORED_DATA12_exception_C.exception_C rv') rv'Base)"
    by (metis tdRESULT_C_accupd_same tdRESULT_C_idupdates(1))
  have "corres_underlying UNIV False True rrel G G' (throwError x1)
           (return (tdRESULT_C (TPM_STORED_DATA12_exception_C.exception_C rv')))"
    by (simp add: error_rel_imp_rrel the_error_rel throwError_def) 
  thus "corres_underlying UNIV False True rrel G G' (throwError x1)
           (return
             (tdRESULT_C.exception_C_update (\<lambda>a. TPM_STORED_DATA12_exception_C.exception_C rv')
               rv'Base))" 
    apply (subst 0[THEN sym]) by simp
qed
  
lemma top_top_top: "\<top> = (\<top> and \<top>)" by simp
lemma x_eq_x_and_top : "x = (x and \<top>)" by simp
lemma x_eq_top_and_x :"x = (\<top> and x)" by simp
lemma x_eq_x_and_x : "x = (x and x)" by auto

lemma trusted_boot_corres:
  "corres (\<lambda> r (r',t'). RESULT_rel r r') \<top> \<top> (trusted_boot idx) (trusted_boot' (of_nat idx))"
  unfolding trusted_boot_def trusted_boot'_def lift_def condition_def
  apply (rule corres_add_noop_lhs)
  apply (subst (1 2) top_top_top)
  apply (rule corres_split[where R'="\<lambda> r' s'. r' = tdRESULT_C (tdEXCEPTION_C NONE)"])
     defer
     apply (auto)
   apply(rule hoare_return_post[where P="\<top>",simplified])
  apply (subst (1) top_top_top)
  apply(subst (7) x_eq_top_and_x)
  unfolding bindE_def
  apply (rule corres_split)
     defer
     prefer 3
     apply (rule hoare_vcg_prop)
    apply (rule read_passphrase_corres)
   apply (rule hoare_post_taut)
  unfolding lift_def
  apply auto
  apply (rename_tac result' sealed_pp sealed_pp')
  apply (rule_tac  Assm=True and  Assm'="returnExRel_TPM_STORED_DATA12 sealed_pp sealed_pp'"
      in extract_assms_from_corres)
    apply auto
   apply (rule R_STORED_DATA_rel_lemma, simp)
  apply (rule simplifyExMonad_TPM_STORED_DATA12)
  apply (auto simp:NONE_def)
   defer
   apply(unfold RESULT_rel_def)[1]
   apply auto
  apply(rule_tac Assm=True and Assm'="result' = tdRESULT_C (tdEXCEPTION_C 0)"
      in extract_assms_from_corres)
    apply auto
  apply (rename_tac sealed_pp_val)  
  apply (subst (1)top_top_top)
  apply (subst (7)x_eq_top_and_x)
  apply (rule corres_split)
     defer
     apply (rule get_authdata_corres)
    apply (rule hoare_post_taut)+
  apply (rename_tac pp_auth pp_auth')
  apply (rule_tac Assm=True and Assm'="R_AUTHDATA_rel pp_auth pp_auth'"
      in extract_assms_from_corres)
    apply auto
  apply (rule simplifyExMonad_TPM_AUTHDATA)           
   apply auto
    apply (rule R_AUTHDATA_rel_lemma, simp)
   apply (subst (1)top_top_top)
   apply (subst (7)x_eq_top_and_x)
   apply (rule corres_split)
      defer
      apply (rule get_authdata_corres)
     apply (rule hoare_post_taut)+
   apply (unfold RESULT_rel_def)[1] apply auto
  apply(rename_tac pp_auth_val srk_auth srk_auth')
  apply (rule_tac Assm=True and Assm' = "R_AUTHDATA_rel srk_auth srk_auth'"
      in extract_assms_from_corres)
    apply auto
  apply (rule simplifyExMonad_TPM_AUTHDATA)
   defer
   apply (unfold RESULT_rel_def)[1]
   apply auto
   apply (rule R_AUTHDATA_rel_lemma,simp)             
  apply (subst (1)top_top_top)
  apply (subst (7)x_eq_top_and_x)
  apply (rule corres_split)
     defer defer
     apply (rule hoare_post_taut)+           
   defer
   apply (rule unseal_passphrase_corres) 
  using R_AUTHDATA_rel_def apply force
  using R_AUTHDATA_rel_def apply force
  apply(rename_tac srk_auth'_value rv rv')
  apply (rule_tac Assm=True and Assm'="returnExRel_CSTRING rv rv'"
      in extract_assms_from_corres)
    apply safe
   apply (rule R_cstring_rel_lemma, simp)
  apply (subst  if_distrib[of return _ _])
  apply (subst simp_if_inside_independent_lambda)
  apply(rule simplifyExMonad_CSTRING)
   defer
   apply (unfold RESULT_rel_def)[1]
   apply auto
  unfolding RESULT_rel_def 
   apply (simp add: returnOk_def2) 
  by (simp add: returnOk_def2)
    
    
    (*lemma refines: "AC_minimal \<sqsubseteq> A_minimal"
proof (rule sim_imp_refines)
  have "A_minimal \<Turnstile> I\<^sub>A" unfolding I\<^sub>A_def by auto
  moreover have "AC_minimal \<Turnstile> I\<^sub>C" unfolding I\<^sub>C_def by auto
  moreover have "LI A_minimal AC_minimal R (I\<^sub>A \<times> I\<^sub>C)"
  proof -
    have "Run A_minimal = lift_nd minimalA" unfolding A_minimal_def by simp
    moreover have "Run AC_minimal = lift_nd minimalAC" unfolding AC_minimal_def by simp
    moreover have "\<forall>s. Init AC_minimal s \<subseteq> (R \<inter> I\<^sub>A \<times> I\<^sub>C) `` Init A_minimal s"
      unfolding AC_minimal_def A_minimal_def R_def I\<^sub>A_def I\<^sub>C_def by auto
    moreover have "corres_underlying R False True \<top>\<top>
      (\<lambda>s\<^sub>A. s\<^sub>A \<in> I\<^sub>A) (\<lambda>s\<^sub>C. s\<^sub>C \<in> I\<^sub>C) minimalA minimalAC" using corres .
    moreover have "\<forall>s s'. (s, s') \<in> R \<inter> I\<^sub>A \<times> I\<^sub>C \<longrightarrow> Fin AC_minimal s' = Fin A_minimal s"
      unfolding AC_minimal_def A_minimal_def R_def I\<^sub>A_def I\<^sub>C_def by auto
    ultimately show ?thesis using corres_LI by blast
  qed
  ultimately show "AC_minimal \<sqsubseteq>\<^sub>F A_minimal"
    using LI_fw_sim and L_invariantI by blas
qed*)

end

end