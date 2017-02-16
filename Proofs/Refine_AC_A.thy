theory Refine_AC_A
imports
  TPM_Corres
begin

context sable_m
begin

definition
  read_passphrase_rel :: "string TPM.STORED_DATA \<Rightarrow> tdTPM_STORED_DATA12_C \<times> lifted_globals \<Rightarrow> bool"
where
  "read_passphrase_rel d d' \<equiv> True"

lemma read_passphrase_corres: "corres read_passphrase_rel \<top> \<top> read_passphrase read_passphrase'"
unfolding read_passphrase_def read_passphrase'_def
proof -
  have "corres read_passphrase_rel \<top> \<top> (do x \<leftarrow> TPM_NV_ReadValue 4 0 None;
                                          case x of Inl e \<Rightarrow> exit_r | Inr b \<Rightarrow> return b
                                         od)
       (do ret' \<leftarrow> (unknown >>= (\<lambda>au. TPM_NV_ReadValue' 4 0 0x190 (hasValue_C_update (\<lambda>_. 0) au) NULL));
           (when (TPM_NV_ReadValue_ret_C.returnCode_C ret' \<noteq> 0) exit' >>=
           (\<lambda>_. unpack_TPM_STORED_DATA12' (TPM_NV_ReadValue_ret_C.data_C ret') (TPM_NV_ReadValue_ret_C.dataSize_C ret')))
        od)" (is "corres _ _ _ (?a >>= ?b) (?c >>= ?d)")
  proof -
    let ?r' = "TPM_NV_ReadValue_rel StoredData_rel"
    let ?R = "\<top>\<top>"
    let ?R' = "\<top>\<top>"
    have "corres ?r' \<top> \<top> ?a ?c"
    apply (rule corres_symb_exec_r [where Q'="\<lambda>_. PO'"])
      using TPM_NV_ReadValue_corres [where P=\<top> and P'=\<top> and idx=4 and idx'=4 and off=0 and off'=0
        and size'="0x190" and s'=NULL and a=None] unfolding comp_def apply simp
      unfolding unknown_def apply (wp select_wp, simp)
      apply clarsimp
      apply (rule_tac Q="\<lambda>s\<^sub>C. (s\<^sub>A, s\<^sub>C) \<in> R" in hoare_weaken_pre)
      apply (wp select_wp, simp_all)
      apply (rule non_fail_select')
    done
    moreover have "\<And>rv rv'. corres read_passphrase_rel (?R rv) (\<lambda>s'. ?r' rv (rv', s') \<and> ?R' rv' s') (?b rv) (?d rv')"
    proof (rule corres_assume_pre)
      fix rv rv' s s'
      assume G: "PO s \<and> True"
         and G': "PO' s' \<and> TPM_NV_ReadValue_rel StoredData_rel rv (rv', s') \<and> True"
         and "(s, s') \<in> R"
      let ?corres_b_d = "corres read_passphrase_rel (?R rv) (\<lambda>s'. ?r' rv (rv', s') \<and> ?R' rv' s')
                    (?b rv) (?d rv')"
      { fix error
        assume rv: "rv = Inl error"
        with G' have rv': "TPM_NV_ReadValue_ret_C.returnCode_C rv' \<noteq> 0"
          unfolding TPM_NV_ReadValue_rel_def ERROR_rel_def TPM_BASE_def by auto
        have "corres \<top>\<top> \<top> \<top> exit exit'" using exit_corres [where P=\<top> and P'=\<top>] by simp
        moreover have "corres_off read_passphrase_rel (\<top>\<top> rv)
          (\<lambda>s'. \<top>\<top> rv (rv', s') \<and> \<top> s') unknown
            (unpack_TPM_STORED_DATA12' (TPM_NV_ReadValue_ret_C.data_C rv')
             (TPM_NV_ReadValue_ret_C.dataSize_C rv'))"
          by (rule corres_off_valid)
        moreover have "\<lbrace>\<top>\<rbrace> exit \<lbrace>\<lambda>_ s. \<not>PO s\<rbrace>" unfolding exit_def by (wp, auto)
        moreover have "\<lbrace>\<top>\<rbrace> exit' \<lbrace>\<lambda>_ s'. \<not>PO' s'\<rbrace>" unfolding exit'_def apply wp
        have ?corres_b_d sorry}
      moreover
      { fix val
        assume rv: "rv = Inr val"
        with G' have rv': "TPM_NV_ReadValue_ret_C.returnCode_C rv' = 0"
          unfolding TPM_NV_ReadValue_rel_def ERROR_rel_def TPM_SUCCESS_def TPM_BASE_def by auto
        have ?corres_b_d sorry}
      ultimately show ?corres_b_d by (meson sum_all_ex(2))
    hence 
 (*   hence 
      { fix error
        assume "rv = Inl error"
        hence "corres read_passphrase_rel \<top> (\<lambda>s'. TPM_NV_ReadValue_rel StoredData_rel rv (rv', s')) exit (?d rv')"
  
  proof (rule corres_split [where r'="\<lambda>s'. TPM_NV_ReadValue_rel StoredData_rel rv (rv', s')" and R="\<top>\<top>" and R'="\<top>\<top>"])
    fix val val'
    let ?goal = "corres (\<lambda>_ _. True) (\<lambda>_. True) (\<lambda>s'. True \<and> True) (case val of Inl e \<Rightarrow> exit | Inr b \<Rightarrow> return b)
               (do _ \<leftarrow> when (TPM_NV_ReadValue_ret_C.returnCode_C val' \<noteq> 0) (exit' (TPM_NV_ReadValue_ret_C.returnCode_C val'));
                   unpack_TPM_STORED_DATA12' (TPM_NV_ReadValue_ret_C.data_C val') (TPM_NV_ReadValue_ret_C.dataSize_C val')
                od)"
    { fix error
      assume "val = Inl error"
      hence "corres (\<lambda>_ _. True) (\<lambda>_. True) (\<lambda>s'. True) exit
               (do _ \<leftarrow> when (TPM_NV_ReadValue_ret_C.returnCode_C val' \<noteq> 0) (exit' (TPM_NV_ReadValue_ret_C.returnCode_C val'));
                   unpack_TPM_STORED_DATA12' (TPM_NV_ReadValue_ret_C.data_C val') (TPM_NV_ReadValue_ret_C.dataSize_C val')
                od)"
      have "?goal" }
  sorry
  thus "corres (\<lambda>_ _. True) (\<lambda>_. True) (\<lambda>_. True) (TPM_NV_ReadValue 4 0 None <catch> (\<lambda>e. exit))
       (do nv_auth___struct_TPM_AUTHDATA_option_C \<leftarrow> unknown;
           ret' \<leftarrow> TPM_NV_ReadValue' 4 0 0x190 (hasValue_C_update (\<lambda>_. 0) nv_auth___struct_TPM_AUTHDATA_option_C) NULL;
           when (TPM_NV_ReadValue_ret_C.returnCode_C ret' \<noteq> 0) (exit' (TPM_NV_ReadValue_ret_C.returnCode_C ret'));
           unpack_TPM_STORED_DATA12' (TPM_NV_ReadValue_ret_C.data_C ret') (TPM_NV_ReadValue_ret_C.dataSize_C ret')
        od)" unfolding catch_def by (simp add: bind_assoc)
qed*)

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