theory RRelation
imports
  TPM_Relation
begin

definition
  TPM_PCRRead_rel :: "(TPM.ERROR + TPM.DIGEST) \<Rightarrow> TPM_PCRRead_ret_C \<Rightarrow> bool"
where
  "TPM_PCRRead_rel r r' \<equiv>
    case r of
      Inl error \<Rightarrow> ERROR_rel error (TPM_PCRRead_ret_C.returnCode_C r')
    | Inr digest \<Rightarrow> DIGEST_rel digest (TPM_PCRRead_ret_C.outDigest_C r')"

end