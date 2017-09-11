theory TPM_Relation
imports
  "../Machine/TPM"
  "../AutoCorres/Impl"
begin

type_synonym heap_data = "8 word ptr \<times> 32 word"

definition
  PCRINDEX_rel :: "TPM.PCRINDEX \<Rightarrow> 32 word \<Rightarrow> bool"
where
  "PCRINDEX_rel i i' \<equiv>
    case i of
      PCR0 \<Rightarrow> i' = 0
    | PCR1 \<Rightarrow> i' = 1
    | PCR2 \<Rightarrow> i' = 2
    | PCR3 \<Rightarrow> i' = 3
    | PCR4 \<Rightarrow> i' = 4
    | PCR5 \<Rightarrow> i' = 5
    | PCR6 \<Rightarrow> i' = 6
    | PCR7 \<Rightarrow> i' = 7
    | PCR8 \<Rightarrow> i' = 8
    | PCR9 \<Rightarrow> i' = 9
    | PCR10 \<Rightarrow> i' = 10
    | PCR11 \<Rightarrow> i' = 11
    | PCR12 \<Rightarrow> i' = 12
    | PCR13 \<Rightarrow> i' = 13
    | PCR14 \<Rightarrow> i' = 14
    | PCR15 \<Rightarrow> i' = 15
    | PCR16 \<Rightarrow> i' = 16
    | PCR17 \<Rightarrow> i' = 17
    | PCR18 \<Rightarrow> i' = 18
    | PCR19 \<Rightarrow> i' = 19
    | PCR20 \<Rightarrow> i' = 20
    | PCR21 \<Rightarrow> i' = 21
    | PCR22 \<Rightarrow> i' = 22
    | PCR23 \<Rightarrow> i' = 23"

value "PCRINDEX_rel PCR7 7" (* True *)
value "PCRINDEX_rel PCR7 8" (* False *)
value "PCRINDEX_rel PCR7 90" (* False *)

definition "TPM_BASE \<equiv> 0 :: 32 word"
definition "TPM_SUCCESS \<equiv> TPM_BASE"

definition
  TPM_ERROR_rel :: "TPM.ERROR \<Rightarrow> 32 word \<Rightarrow> bool"
where
  "TPM_ERROR_rel e e' \<equiv> if e' = TPM_BASE then False else
    case e of
      AUTHFAIL \<Rightarrow> e' = TPM_BASE + 1
    | OTHER_ERROR \<Rightarrow> e' > TPM_BASE + 1 \<and> e' \<le> TPM_BASE + 99"

value "TPM_ERROR_rel AUTHFAIL 1" (* True *)
value "TPM_ERROR_rel OTHER_ERROR 1" (* False *)

definition
  TPM_RESULT_rel :: "(TPM.ERROR + unit) \<Rightarrow> 32 word \<Rightarrow> bool"
where
  "TPM_RESULT_rel r r' \<equiv>
    case r of
      Inl error \<Rightarrow> TPM_ERROR_rel error r'
    | Inr _ \<Rightarrow> r' = TPM_SUCCESS"

value "TPM_RESULT_rel (Inr ()) 0" (* True *)
value "TPM_RESULT_rel (Inr ()) 1" (* False *)
value "TPM_RESULT_rel (Inl AUTHFAIL) 1" (* True *)

definition
  ERROR_rel :: "ERROR \<Rightarrow> 32 signed word \<Rightarrow> bool"
where
  "ERROR_rel e e' \<equiv> e' \<noteq> NONE \<and>
    (case e of
      E_BAD_ELF_HEADER \<Rightarrow> e' = ERROR_BAD_ELF_HEADER
    | E_SHA1_DATA_SIZE \<Rightarrow> e' = ERROR_SHA1_DATA_SIZE
    | E_NO_MODULE \<Rightarrow> e' = ERROR_NO_MODULE
    | E_BAD_MODULE \<Rightarrow> e' = ERROR_BAD_MODULE
    | E_BAD_MBI \<Rightarrow> e' = ERROR_BAD_MBI
    | E_NO_MBI \<Rightarrow> e' = ERROR_NO_MBI
    | E_BAD_TPM_VENDOR \<Rightarrow> e' = ERROR_BAD_TPM_VENDOR
    | E_TIS_TRANSMIT \<Rightarrow> e' = ERROR_TIS_TRANSMIT
    | E_TIS_LOCALITY_REGISTER_INVALID \<Rightarrow> e' = ERROR_TIS_LOCALITY_REGISTER_INVALID
    | E_TIS_LOCALITY_ACCESS_TIMEOUT \<Rightarrow> e' = ERROR_TIS_LOCALITY_ACCESS_TIMEOUT
    | E_TIS_LOCALITY_ALREADY_ACCESSED \<Rightarrow> e' = ERROR_TIS_LOCALITY_ALREADY_ACCESSED
    | E_TIS_LOCALITY_DEACTIVATE \<Rightarrow> e' = ERROR_TIS_LOCALITY_DEACTIVATE
    | E_PCI \<Rightarrow> e' = ERROR_PCI
    | E_APIC \<Rightarrow> e' = ERROR_APIC
    | E_DEV \<Rightarrow> e' = ERROR_DEV
    | E_SVM_ENABLE \<Rightarrow> e' = ERROR_SVM_ENABLE
    | E_NO_EXT \<Rightarrow> e' = ERROR_NO_EXT
    | E_NO_APIC \<Rightarrow> e' = ERROR_NO_APIC
    | E_NO_SVM \<Rightarrow> e' = ERROR_NO_SVM
    | E_BUFFER_OVERFLOW \<Rightarrow> e' = ERROR_BUFFER_OVERFLOW
    | E_TPM_BAD_OUTPUT_PARAM \<Rightarrow> e' = ERROR_TPM_BAD_OUTPUT_PARAM
    | E_TPM_BAD_OUTPUT_AUTH \<Rightarrow> e' = ERROR_TPM_BAD_OUTPUT_AUTH
    | E_TPM tpme \<Rightarrow> \<exists>tpme'. e' = (1 << 7) || tpme' \<and> TPM_ERROR_rel tpme (scast tpme'))"

definition
  BOOL_rel :: "bool \<Rightarrow> 8 word \<Rightarrow> bool"
where
  "BOOL_rel b b' \<equiv> b \<longleftrightarrow> b' \<noteq> 0"

value "BOOL_rel True 14" (* True *)
value "BOOL_rel False 14" (* False *)
value "BOOL_rel False 0" (* True *)

(* This relation is axiomatized *)
consts DIGEST_rel :: "TPM.DIGEST \<Rightarrow> tdTPM_DIGEST_C \<Rightarrow> bool"

(* This relation is axiomatized *)
consts NONCE_rel :: "TPM.NONCE \<Rightarrow> tdTPM_NONCE_C \<Rightarrow> bool"

(* This relation is axiomatized *)
consts AUTHDATA_rel :: "TPM.AUTHDATA \<Rightarrow> tdTPM_AUTHDATA_C \<Rightarrow> bool"

(* FIXME *)
definition
  ENTITY_TYPE_rel :: "TPM.ENTITY_TYPE \<Rightarrow> 16 word \<Rightarrow> bool"
where
  "ENTITY_TYPE_rel t t' \<equiv> True"

definition
  LOCALITY_rel :: "TPM.LOCALITY \<Rightarrow> 8 word \<Rightarrow> bool"
where
  "LOCALITY_rel l l' \<equiv>
    case l of
      LOC_ZERO \<Rightarrow> l' = 1 << 0
    | LOC_ONE \<Rightarrow> l' = 1 << 1
    | LOC_TWO \<Rightarrow> l' = 1 << 2
    | LOC_THREE \<Rightarrow> l' = 1 << 3
    | LOC_FOUR \<Rightarrow> l' = 1 << 4"

definition
  LOCALITY_SELECTION_rel :: "TPM.LOCALITY_SELECTION \<Rightarrow> 8 word \<Rightarrow> bool"
where
  "LOCALITY_SELECTION_rel l l' \<equiv> \<forall>loc \<in> l. \<exists>mask. LOCALITY_rel loc (l' AND mask)"

(* FIXME *)
(*definition
  PCR_SELECTION_rel :: "TPM.PCR_SELECTION \<Rightarrow> tdTPM_PCR_SELECTION_C \<times> lifted_globals \<Rightarrow> bool"
where
  "PCR_SELECTION_rel p p' \<equiv> True"

definition
  PCR_INFO_LONG_rel :: "TPM.PCR_INFO_LONG \<Rightarrow> tdTPM_PCR_INFO_LONG_C \<times> lifted_globals \<Rightarrow> bool"
where
  "PCR_INFO_LONG_rel i i' \<equiv>
    tdTPM_PCR_INFO_LONG_C.tag_C (fst i') = 0x0006 \<and>
    LOCALITY_SELECTION_rel (TPM.PCR_INFO_LONG.localityAtCreation i)
      (tdTPM_PCR_INFO_LONG_C.localityAtCreation_C (fst i')) \<and>
    LOCALITY_SELECTION_rel (TPM.PCR_INFO_LONG.localityAtRelease i)
      (tdTPM_PCR_INFO_LONG_C.localityAtRelease_C (fst i')) \<and>
    PCR_SELECTION_rel (TPM.PCR_INFO_LONG.creationPCRSelection i)
      (tdTPM_PCR_INFO_LONG_C.creationPCRSelection_C (fst i'), snd i') \<and>
    PCR_SELECTION_rel (TPM.PCR_INFO_LONG.releasePCRSelection i)
      (tdTPM_PCR_INFO_LONG_C.releasePCRSelection_C (fst i'), snd i') \<and>
    DIGEST_rel (TPM.PCR_INFO_LONG.digestAtCreation i)
      (tdTPM_PCR_INFO_LONG_C.digestAtCreation_C (fst i')) \<and>
    DIGEST_rel (TPM.PCR_INFO_LONG.digestAtRelease i)
      (tdTPM_PCR_INFO_LONG_C.digestAtRelease_C (fst i'))"*)

definition
  PAYLOAD_TYPE_rel :: "PAYLOAD_TYPE \<Rightarrow> 8 word \<Rightarrow> bool"
where
  "PAYLOAD_TYPE_rel p p' \<equiv> case p of PT_SEAL \<Rightarrow> p' = 5"

(* We don't care about this yet
definition
  SEALED_DATA_rel :: "(('a :: Hashable) \<Rightarrow> (8 word ptr \<times> 32 word) \<times> lifted_globals \<Rightarrow> bool)
    \<Rightarrow> 'a TPM.SEALED_DATA
    \<Rightarrow> tdTPM_SEALED_DATA_C \<times> lifted_globals \<Rightarrow> bool"
where
  "SEALED_DATA_rel vrel d d' \<equiv>
    PAYLOAD_TYPE_rel (TPM.SEALED_DATA.payload d) (tdTPM_SEALED_DATA_C.payload_C (fst d')) \<and>
    AUTHDATA_rel (TPM.SEALED_DATA.authData d) (tdTPM_SEALED_DATA_C.authData_C (fst d')) \<and>
    AUTHDATA_rel (TPM.SEALED_DATA.tpmProof d) (tdTPM_SEALED_DATA_C.tpmProof_C (fst d')) \<and>
    DIGEST_rel (TPM.SEALED_DATA.storedDigest d) (tdTPM_SEALED_DATA_C.storedDigest_C (fst d')) \<and>
    vrel (TPM.SEALED_DATA.data d) ((tdTPM_SEALED_DATA_C.data_C (fst d'),
      tdTPM_SEALED_DATA_C.dataSize_C (fst d')), snd d')"
*)

(* Bogus for now *)
definition
  STORED_DATA_rel :: "(('a :: Hashable) \<Rightarrow> heap_data \<times> lifted_globals \<Rightarrow> bool)
    \<Rightarrow> 'a TPM.STORED_DATA \<Rightarrow> tdTPM_STORED_DATA12_C \<times> lifted_globals \<Rightarrow> bool"
where
  "STORED_DATA_rel vrel d d' \<equiv> True"

end