theory TPM_Corres
imports
  RRelation
  StateRelation
  "../lib/NondetCorres"
  "../lib/WP_Extras"
begin

context sable_isa
begin

abbreviation "SR \<equiv> UNIV"

(* FIXME use state relation *)
abbreviation "corres \<equiv> corres_underlying SR False True"

end

locale sable_m = sable_isa +
  assumes get_authdata_corres: "corres (\<lambda>r r'. R_AUTHDATA_rel r (fst r'))
                                  \<top> \<top> get_authdata get_authdata'"

      and get_nonce_corres: "corres (\<lambda>r r'. R_NONCE_rel r (fst r')) \<top> \<top> get_nonce get_nonce'"

      and TPM_PCRRead_corres: "\<And>i i'. PCRINDEX_rel i i' \<Longrightarrow>
        corres (\<lambda>r r'. R_PCRVALUE_rel r (fst r')) \<top> \<top> (TPM_PCRRead i) (TPM_PCRRead' i')"

      and TPM_OIAP_corres: "\<And>sess'. corres (\<lambda>r r'. RESULT_rel r (fst r'))
          \<top> (\<lambda>s'. is_valid_tdTPM_SESSION_C'ptr s' sess') TPM_OIAP (TPM_OIAP' sess')"

      and no_fail_unpack_TPM_STORED_DATA12':
        "\<And>P d dSize. no_fail P (unpack_TPM_STORED_DATA12' d dSize)"

      (* FIXME: add constraints to the authdata/session inputs *)
      and TPM_NV_ReadValue_corres: "\<And>P P' idx idx' off off' a size' ownerAuth' s'.
        \<lbrakk>idx' = of_nat idx; off' = of_nat off\<rbrakk>
        \<Longrightarrow> corres (R_HEAP_DATA_rel (E_STORED_DATA_rel string_rel)) P P'
        (TPM_NV_ReadValue idx off a) (TPM_NV_ReadValue' idx' off' size' ownerAuth' s')"

print_locale! sable_m

end