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
    | Inr digest \<Rightarrow> TPM_PCRRead_ret_C.returnCode_C r' = 0 \<and>
        DIGEST_rel digest (TPM_PCRRead_ret_C.outDigest_C r')"

definition
  TPM_NV_ReadValue_rel :: "(('a :: Hashable) \<Rightarrow> (8 word ptr \<times> 32 word) \<times> lifted_globals \<Rightarrow> bool)
                          \<Rightarrow> TPM.ERROR + 'a
                          \<Rightarrow> TPM_NV_ReadValue_ret_C \<times> lifted_globals
                          \<Rightarrow> bool"
where
  "TPM_NV_ReadValue_rel vrel r r' \<equiv>
    case r of
      Inl e \<Rightarrow> ERROR_rel e (TPM_NV_ReadValue_ret_C.returnCode_C (fst r'))
    | Inr v \<Rightarrow> TPM_NV_ReadValue_ret_C.returnCode_C (fst r') = TPM_SUCCESS \<and>
        vrel v ((TPM_NV_ReadValue_ret_C.data_C (fst r'),
        TPM_NV_ReadValue_ret_C.dataSize_C (fst r')), snd r')"

end