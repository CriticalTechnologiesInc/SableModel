theory TPM_Relation
imports
  "../Machine/TPM"
  "../AutoCorres/Impl"
begin

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
  ERROR_rel :: "TPM.ERROR \<Rightarrow> 32 word \<Rightarrow> bool"
where
  "ERROR_rel e e' \<equiv> if e' = TPM_BASE then False else
    case e of
      AUTHFAIL \<Rightarrow> e' = TPM_BASE + 1
    | OTHER_ERROR \<Rightarrow> e' > TPM_BASE + 1 \<and> e' \<le> TPM_BASE + 99"

value "ERROR_rel AUTHFAIL 1" (* True *)
value "ERROR_rel OTHER_ERROR 1" (* False *)

definition
  RESULT_rel :: "(TPM.ERROR + unit) \<Rightarrow> 32 word \<Rightarrow> bool"
where
  "RESULT_rel r r' \<equiv>
    case r of
      Inl error \<Rightarrow> ERROR_rel error r'
    | Inr _ \<Rightarrow> r' = TPM_SUCCESS"

value "RESULT_rel (Inr ()) 0" (* True *)
value "RESULT_rel (Inr ()) 1" (* False *)
value "RESULT_rel (Inl AUTHFAIL) 1" (* True *)

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
definition
  PCR_SELECTION_rel :: "TPM.PCR_SELECTION \<Rightarrow> tdTPM_PCR_SELECTION_C \<times> lifted_globals \<Rightarrow> bool"
where
  "PCR_SELECTION_rel p p' \<equiv> True"

definition
  PCR_INFO_LONG_rel :: "TPM.PCR_INFO_LONG \<Rightarrow> tdTPM_PCR_INFO_LONG_C \<times> lifted_globals \<Rightarrow> bool"
where
  "PCR_INFO_LONG_rel i i' \<equiv>
    tdTPM_PCR_INFO_LONG_C.tag_C (fst i') = 6 \<and>
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
      (tdTPM_PCR_INFO_LONG_C.digestAtRelease_C (fst i'))"

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
  STORED_DATA_rel :: "(('a :: Hashable) \<Rightarrow> (8 word ptr \<times> 32 word) \<times> lifted_globals \<Rightarrow> bool)
    \<Rightarrow> 'a TPM.STORED_DATA \<Rightarrow> tdTPM_STORED_DATA12_C \<times> lifted_globals \<Rightarrow> bool"
where
  "STORED_DATA_rel vrel d d' \<equiv> True"

(* Function return relations *)

(* FIXME
definition
  ReadValue_STORED_DATA_rel :: "('a :: Hashable) TPM.STORED_DATA
    \<Rightarrow> (8 word ptr \<times> 32 word) \<times> lifted_globals \<Rightarrow> bool"
where
  "ReadValue_STORED_DATA_rel d d' \<equiv>
    let s' = snd d' in
    let ptr' = fst (fst d') in
    let size' = snd (fst d') in
    vrel d " *)

end