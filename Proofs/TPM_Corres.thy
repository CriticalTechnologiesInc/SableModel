theory TPM_Corres
imports
  RRelation
  StateRelation
  "../lib/NondetCorres"
  "../lib/WP_Extras"
begin

context sable_verified
begin

abbreviation "PO \<equiv> powerOn \<circ> machine"
abbreviation "PO' \<equiv> powerOn \<circ> phantom_machine_state_''"
abbreviation "corres \<equiv> \<lambda>rrel G G'. corres_underlying R False True rrel
                (\<lambda>s. PO s \<and> G s) (\<lambda>s'. PO' s' \<and> G' s')"
abbreviation "corres_off \<equiv> \<lambda>rrel G G'. corres_underlying R False True rrel
                (\<lambda>s. \<not>PO s \<and> G s) (\<lambda>s'. \<not>PO' s' \<and> G' s')"

lemma corres_off_valid: "\<And>rrel G G' m m'. corres_off rrel G G' m m'"
unfolding R_def corres_underlying_def by auto

(* FIXME: reason about size, value *)
definition
  StoredData_rel :: "string TPM.STORED_DATA \<Rightarrow> (8 word ptr \<times> 32 word) \<times> lifted_globals \<Rightarrow> bool"
where
  "StoredData_rel d d' \<equiv> case d' of ((v', size'), s') \<Rightarrow>
    \<forall>p \<in> fst (unpack_TPM_STORED_DATA12' v' size' s'). STORED_DATA_rel \<top>\<top> d p"

end

locale sable_m = sable_verified +
  assumes get_authdata_corres: "corres (\<lambda>r r'. AUTHDATA_rel r (fst r'))
                                  \<top> \<top> get_authdata get_authdata'"

      and get_nonce_corres: "corres (\<lambda>r r'. NONCE_rel r (fst r')) \<top> \<top> get_nonce get_nonce'"

      and exit_corres: "\<And>P P'. corres \<top>\<top> P P' exit exit'"

      and TPM_PCRRead_corres: "\<And>i i'. PCRINDEX_rel i i' \<Longrightarrow>
        corres (\<lambda>r r'. TPM_PCRRead_rel r (fst r')) \<top> \<top> (TPM_PCRRead i) (TPM_PCRRead' i')"

      and TPM_OIAP_corres: "\<And>sess'. corres (\<lambda>r r'. RESULT_rel r (fst r'))
          \<top> (\<lambda>s'. is_valid_tdTPM_SESSION_C'ptr s' sess') TPM_OIAP (TPM_OIAP' sess')"

      (* FIXME: add constraints to the authdata/session inputs *)
      and TPM_NV_ReadValue_corres: "\<And>P P' idx idx' off off' a size' ownerAuth' s'.
        \<lbrakk>idx' = of_nat idx; off' = of_nat off\<rbrakk>
        \<Longrightarrow> corres (TPM_NV_ReadValue_rel StoredData_rel) P P' (TPM_NV_ReadValue idx off a)
        (TPM_NV_ReadValue' idx' off' size' ownerAuth' s')"

context sable_m
begin

lemma exit: "\<lbrace>\<top>\<rbrace> exit \<lbrace>\<lambda>_ s. \<not>PO s\<rbrace>"
unfolding exit_def apply wp

lemma exit': "\<lbrace>\<top>\<rbrace> exit' \<lbrace>\<lambda>_ s'. \<not>PO' s'\<rbrace>"
using exit_corres

end

end