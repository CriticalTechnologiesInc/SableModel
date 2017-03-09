theory Refine_AC_A
imports
  TPM_Corres
begin

context sable_m
begin

lemma read_passphrase_corres:
  "corres (R_STORED_DATA_rel string_rel) \<top> \<top> (read_passphrase i) (read_passphrase' (of_nat i))"
  (is "corres ?r _ _ _ _")
unfolding read_passphrase_def read_passphrase'_def
proof simp
  let ?r' = "R_HEAP_DATA_rel (E_STORED_DATA_rel string_rel)"
  show "corres ?r \<top> \<top> (TPM_NV_ReadValue i 0 None)
       (do ret' \<leftarrow> TPM_NV_ReadValue' (of_nat i) 0 0x190 (TPM_AUTHDATA_option_C (tdTPM_AUTHDATA_C (ARRAY _. 0)) 0) NULL;
         condition (\<lambda>s. error_C (HEAP_DATA_exception_C.exception_C ret') \<noteq> 0)
           (return (TPM_STORED_DATA12_exception_C (HEAP_DATA_exception_C.exception_C ret')
              (tdTPM_STORED_DATA12_C 0 0 0 NULL 0 NULL)))
           (do ret' \<leftarrow>
               unpack_TPM_STORED_DATA12' (tdHEAP_DATA_C.data_C (HEAP_DATA_exception_C.value_C ret'))
                (tdHEAP_DATA_C.dataSize_C (HEAP_DATA_exception_C.value_C ret'));
               return (TPM_STORED_DATA12_exception_C (tdEXCEPTION_C NONE) ret')
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
      with Inl have rv': "error_C (HEAP_DATA_exception_C.exception_C rv') \<noteq> NONE"
        unfolding R_HEAP_DATA_rel_def ERROR_rel_def by simp
      hence "?c rv' s'" by (simp add: NONE_def)
      from Inl and rv' have "corres ?r \<top> (\<lambda>s'. ?r' rv (rv', s')) (return rv) (?t rv')"
        by (simp add: R_HEAP_DATA_rel_def R_STORED_DATA_rel_def)
      thus ?thesis using `?c rv' s'` by auto
    next
      let ?error = "error_C (HEAP_DATA_exception_C.exception_C rv')"
      let ?data = "tdHEAP_DATA_C.data_C (HEAP_DATA_exception_C.value_C rv')"
      let ?dataSize = "tdHEAP_DATA_C.dataSize_C (HEAP_DATA_exception_C.value_C rv')"
      case (Inr v)
      fix s'
      assume "?r' rv (rv', s')"
      with Inr have rv'_e: "?error = NONE" unfolding R_HEAP_DATA_rel_def ERROR_rel_def by simp
      hence "\<not>?c rv' s'" by (simp add: NONE_def)
      from Inr and `?r' rv (rv', s')` have rv'_v:
        "HEAP_DATA_rel (E_STORED_DATA_rel string_rel) v (HEAP_DATA_exception_C.value_C rv', s')"
        unfolding R_HEAP_DATA_rel_def by simp
      hence unpack: "\<forall>r \<in> fst (unpack_TPM_STORED_DATA12' ?data ?dataSize s').
          STORED_DATA_rel string_rel v r"
        unfolding HEAP_DATA_rel_def E_STORED_DATA_rel_def by simp
      let ?r'' = "\<lambda>rv rv'. case rv of Inl e \<Rightarrow> False | Inr v \<Rightarrow> STORED_DATA_rel string_rel v rv'"
      let ?unpack = "unpack_TPM_STORED_DATA12' ?data ?dataSize"
      have "corres ?r \<top> (\<lambda>s'. ?r' (Inr v) (rv', s')) (return (Inr v)) (?f rv')"
      apply (rule corres_bind_return)
      proof (rule corres_split' [where r'="?r''" and Q="\<top>\<top>" and Q'="\<top>\<top>"])
        have p: "\<forall>(s, s') \<in> SR. ?r' (Inr v) (rv', s') \<longrightarrow> (\<forall>(r', t') \<in> fst (?unpack s').
              \<exists>(r, t) \<in> fst (return (Inr v) s). (t, t') \<in> SR \<and> ?r'' r (r', t'))"
          unfolding R_HEAP_DATA_rel_def STORED_DATA_rel_def return_def by simp
        with no_fail_unpack_TPM_STORED_DATA12'
          show "corres ?r'' \<top> (\<lambda>s'. ?r' (Inr v) (rv', s')) (return (Inr v)) ?unpack"
          by (fast intro!: corres_no_failI)
      next
        show "\<And>rv rv'. corres ?r \<top> (\<lambda>s'. ?r'' rv (rv', s') \<and> True) (return rv)
          (return (TPM_STORED_DATA12_exception_C (tdEXCEPTION_C NONE) rv'))"
          by (case_tac rv, auto simp add: R_STORED_DATA_rel_def STORED_DATA_rel_def)
      next show "\<lbrace>\<top>\<rbrace> return (Inr v) \<lbrace>\<top>\<top>\<rbrace>" by (rule hoare_post_taut)
      next show "\<lbrace>\<lambda>s'. ?r' (Inr v) (rv', s')\<rbrace> ?unpack \<lbrace>\<top>\<top>\<rbrace>" by (rule hoare_post_taut)
      qed
      thus ?thesis using Inr and `\<not>?c rv' s'` by simp
    qed
  next show "corres ?r' \<top> \<top> ?read ?read'" using TPM_NV_ReadValue_corres
         by (metis of_nat_numeral semiring_1_class.of_nat_0)
  next show "\<lbrace>\<top>\<rbrace> ?read \<lbrace>\<top>\<top>\<rbrace>" by (rule hoare_post_taut)
  next show"\<lbrace>\<lambda>_. True\<rbrace> ?read' \<lbrace>\<lambda>_ _. True\<rbrace>" by (rule hoare_post_taut)
  qed
qed

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