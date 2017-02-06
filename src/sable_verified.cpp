# 1 "/Users/scottconstable/Documents/SU_Graduate/SABLE/sable/src/sable_verified.c"
# 1 "<built-in>" 1
# 1 "<built-in>" 3
# 330 "<built-in>" 3
# 1 "<command line>" 1
# 1 "<built-in>" 2
# 1 "/Users/scottconstable/Documents/SU_Graduate/SABLE/sable/src/sable_verified.c" 2
# 1 "/Users/scottconstable/Documents/SU_Graduate/SABLE/sable/build/include/sable_verified.h" 1

void trusted_boot(void);
typedef unsigned long UINT32;
typedef UINT32 TPM_RESULT;
typedef struct tdTPM_STORED_DATA12 tdTPM_STORED_DATA12;
typedef unsigned short UINT16;
typedef UINT16 TPM_STRUCTURE_TAG;
typedef UINT16 TPM_ENTITY_TYPE;






typedef unsigned char BYTE;
struct tdTPM_STORED_DATA12 {
  TPM_STRUCTURE_TAG tag;
  TPM_ENTITY_TYPE et;
  UINT32 sealInfoSize;

  BYTE *sealInfo;
  UINT32 encDataSize;

  BYTE *encData;
};
typedef struct tdTPM_STORED_DATA12 TPM_STORED_DATA12;
typedef UINT32 TPM_KEY_HANDLE;
typedef struct tdTPM_AUTHDATA tdTPM_AUTHDATA;

struct tdTPM_AUTHDATA {
  BYTE authdata[0x14];
};
typedef struct tdTPM_AUTHDATA TPM_AUTHDATA;
typedef struct tdTPM_SESSION tdTPM_SESSION;
typedef UINT32 TPM_AUTHHANDLE;
typedef struct tdTPM_NONCE tdTPM_NONCE;

struct tdTPM_NONCE {
  BYTE nonce[0x14];
};
typedef struct tdTPM_NONCE TPM_NONCE;
typedef BYTE TPM_BOOL;
struct tdTPM_SESSION {
  TPM_AUTHHANDLE authHandle;
  TPM_NONCE nonceEven;
  TPM_NONCE nonceOdd;
  TPM_BOOL continueAuthSession;
};
typedef struct tdTPM_SESSION TPM_SESSION;
TPM_RESULT TPM_Unseal(TPM_STORED_DATA12 inData_in,BYTE *secret_out,UINT32 secretSizeMax,TPM_KEY_HANDLE parentHandle_in,TPM_AUTHDATA parentAuth,TPM_SESSION *parentSession,TPM_AUTHDATA dataAuth,TPM_SESSION *dataSession);
void unseal_passphrase(TPM_AUTHDATA srk_auth,TPM_AUTHDATA pp_auth,TPM_STORED_DATA12 sealed_pp);
TPM_STORED_DATA12 unpack_TPM_STORED_DATA12(const BYTE *data,UINT32 dataSize);


typedef UINT32 TPM_NV_INDEX;





struct TPM_AUTHDATA_option { TPM_AUTHDATA value; char hasValue; };






TPM_RESULT TPM_NV_ReadValue(BYTE *data_out,TPM_NV_INDEX nvIndex_in,UINT32 offset_in,UINT32 dataSize_in,struct TPM_AUTHDATA_option ownerAuth_in,TPM_SESSION *session);
TPM_STORED_DATA12 read_passphrase(void);


typedef char bool;
int get_string(char *str,unsigned int strSize,bool show);

void out_string(const char *value);






void configure(void);
TPM_RESULT TPM_NV_WriteValueAuth(const BYTE *data_in,UINT32 dataSize_in,TPM_NV_INDEX nvIndex_in,UINT32 offset_in,TPM_AUTHDATA nv_auth,TPM_SESSION *session);
TPM_RESULT TPM_OIAP(TPM_SESSION *session);
void write_passphrase(TPM_AUTHDATA nv_auth);
typedef struct TPM_Seal_ret TPM_Seal_ret;
struct TPM_Seal_ret {
  TPM_RESULT returnCode;
  TPM_STORED_DATA12 sealedData;
};
typedef TPM_AUTHDATA TPM_ENCAUTH;
typedef struct tdTPM_PCR_INFO_LONG tdTPM_PCR_INFO_LONG;
typedef BYTE TPM_LOCALITY_SELECTION;
typedef struct tdTPM_PCR_SELECTION tdTPM_PCR_SELECTION;
struct tdTPM_PCR_SELECTION {
  UINT16 sizeOfSelect;

  BYTE *pcrSelect;
};
typedef struct tdTPM_PCR_SELECTION TPM_PCR_SELECTION;
typedef struct tdTPM_DIGEST tdTPM_DIGEST;
struct tdTPM_DIGEST { BYTE digest[0x14]; };
typedef struct tdTPM_DIGEST TPM_DIGEST;
typedef TPM_DIGEST TPM_COMPOSITE_HASH;
struct tdTPM_PCR_INFO_LONG {
  TPM_STRUCTURE_TAG tag;
  TPM_LOCALITY_SELECTION localityAtCreation;
  TPM_LOCALITY_SELECTION localityAtRelease;
  TPM_PCR_SELECTION creationPCRSelection;
  TPM_PCR_SELECTION releasePCRSelection;
  TPM_COMPOSITE_HASH digestAtCreation;
  TPM_COMPOSITE_HASH digestAtRelease;
};
typedef struct tdTPM_PCR_INFO_LONG TPM_PCR_INFO_LONG;
typedef TPM_AUTHDATA TPM_SECRET;
struct TPM_Seal_ret TPM_Seal(BYTE *rawData,UINT32 rawDataSize,TPM_KEY_HANDLE keyHandle_in,TPM_ENCAUTH encAuth_in,TPM_PCR_INFO_LONG pcrInfo_in,const BYTE *inData_in,UINT32 inDataSize_in,TPM_SESSION *session,TPM_SECRET sharedSecret);
TPM_ENCAUTH encAuth_gen(TPM_AUTHDATA entityAuthData,TPM_SECRET sharedSecret,TPM_NONCE authLastNonceEven);
TPM_SECRET sharedSecret_gen(TPM_AUTHDATA auth,TPM_NONCE nonceEvenOSAP,TPM_NONCE nonceOddOSAP);





typedef struct tdTPM_OSAP_SESSION tdTPM_OSAP_SESSION;
struct tdTPM_OSAP_SESSION {
  TPM_SESSION session;
  TPM_NONCE nonceEvenOSAP;
  TPM_NONCE nonceOddOSAP;
};
typedef struct tdTPM_OSAP_SESSION TPM_OSAP_SESSION;
TPM_RESULT TPM_OSAP(TPM_ENTITY_TYPE entityType_in,UINT32 entityValue_in,TPM_OSAP_SESSION *osap_session);
void seal_passphrase(TPM_AUTHDATA srk_auth,TPM_AUTHDATA pp_auth,UINT32 lenPassphrase);


typedef struct tdTPM_PCR_COMPOSITE tdTPM_PCR_COMPOSITE;
typedef TPM_DIGEST TPM_PCRVALUE;
struct tdTPM_PCR_COMPOSITE {
  TPM_PCR_SELECTION select;
  UINT32 valueSize;

  TPM_PCRVALUE *pcrValue;
};
typedef struct tdTPM_PCR_COMPOSITE TPM_PCR_COMPOSITE;
TPM_COMPOSITE_HASH get_TPM_COMPOSITE_HASH(TPM_PCR_COMPOSITE comp);
# 153 "/Users/scottconstable/Documents/SU_Graduate/SABLE/sable/build/include/sable_verified.h"
const char *tpm_error_to_string(TPM_RESULT res);
void wait(int ms);
void exit(unsigned status)__attribute__((noreturn));
# 164 "/Users/scottconstable/Documents/SU_Graduate/SABLE/sable/build/include/sable_verified.h"
typedef struct TPM_PCRRead_ret TPM_PCRRead_ret;
struct TPM_PCRRead_ret {
  TPM_RESULT returnCode;
  TPM_PCRVALUE outDigest;
};
typedef UINT32 TPM_PCRINDEX;
struct TPM_PCRRead_ret TPM_PCRRead(TPM_PCRINDEX pcrIndex_in);
TPM_PCR_INFO_LONG get_pcr_info(void);
TPM_NONCE get_nonce(void);
TPM_AUTHDATA get_authdata(void);
# 2 "/Users/scottconstable/Documents/SU_Graduate/SABLE/sable/src/sable_verified.c" 2




extern TPM_AUTHDATA get_authdata(void);
extern TPM_NONCE get_nonce(void);





static char passphrase[128];
static BYTE pp_blob[400];
static BYTE pcr_select_bytes[3] = {0x0, 0x0, 0xa};
static const TPM_PCR_SELECTION pcr_select = {
    .sizeOfSelect = sizeof(pcr_select_bytes),
    .pcrSelect = (BYTE *)pcr_select_bytes};
static TPM_PCRVALUE pcr_values[2];


static TPM_OSAP_SESSION srk_osap_session;
static TPM_SESSION nv_session;
static TPM_SESSION srk_session;
static TPM_SESSION pp_session;






TPM_PCR_INFO_LONG get_pcr_info(void) {
  struct TPM_PCRRead_ret pcr17 = TPM_PCRRead(17);
  { if (pcr17.returnCode) { ; exit(pcr17.returnCode); } };
  pcr_values[0] = pcr17.outDigest;
  struct TPM_PCRRead_ret pcr19 = TPM_PCRRead(19);
  { if (pcr19.returnCode) { ; exit(pcr19.returnCode); } };
  pcr_values[1] = pcr19.outDigest;
  TPM_PCR_COMPOSITE composite = {.select = pcr_select,
                                 .valueSize = sizeof(pcr_values),
                                 .pcrValue = (TPM_PCRVALUE *)pcr_values};
  TPM_COMPOSITE_HASH composite_hash = get_TPM_COMPOSITE_HASH(composite);
  TPM_PCR_INFO_LONG pcr_info = {.tag = ((UINT16)0x0006),
                                .localityAtCreation = (((UINT32)1) << 2),
                                .localityAtRelease = (((UINT32)1) << 2),
                                .creationPCRSelection = pcr_select,
                                .releasePCRSelection = pcr_select,
                                .digestAtCreation = composite_hash,
                                .digestAtRelease = composite_hash};
  return pcr_info;
}

void seal_passphrase(TPM_AUTHDATA srk_auth, TPM_AUTHDATA pp_auth,
                     UINT32 lenPassphrase) {
  TPM_RESULT res;


  srk_osap_session.nonceOddOSAP = get_nonce();
  res = TPM_OSAP(((UINT16)0x0001), ((UINT32)0x40000000), &srk_osap_session);
  { if (res) { ; exit(res); } };
  srk_osap_session.session.continueAuthSession = 0x00;


  TPM_SECRET sharedSecret = sharedSecret_gen(
      srk_auth, srk_osap_session.nonceEvenOSAP, srk_osap_session.nonceOddOSAP);


  srk_osap_session.session.nonceOdd = get_nonce();


  TPM_ENCAUTH encAuth =
      encAuth_gen(pp_auth, sharedSecret, srk_osap_session.session.nonceEven);

  TPM_PCR_INFO_LONG pcr_info = get_pcr_info();


  struct TPM_Seal_ret seal_ret =
      TPM_Seal(pp_blob, sizeof(pp_blob), ((UINT32)0x40000000), encAuth, pcr_info,
               (const BYTE *)passphrase, lenPassphrase,
               &srk_osap_session.session, sharedSecret);
  { if (seal_ret.returnCode) { ; exit(seal_ret.returnCode); } };
}

void write_passphrase(TPM_AUTHDATA nv_auth) {
  TPM_RESULT res;

  res = TPM_OIAP(&nv_session);
  { if (res) { ; exit(res); } };

  res = TPM_NV_WriteValueAuth(pp_blob, sizeof(pp_blob), 0x04, 0, nv_auth,
                              &nv_session);
  { if (res) { ; exit(res); } };
}

void configure(void) {



  UINT32 lenPassphrase =
      get_string(passphrase, sizeof(passphrase) - 1, 1) + 1;


  TPM_AUTHDATA pp_auth = get_authdata();


  TPM_AUTHDATA srk_auth = get_authdata();


  seal_passphrase(srk_auth, pp_auth, lenPassphrase);



  TPM_AUTHDATA nv_auth = get_authdata();


  write_passphrase(nv_auth);
}

TPM_STORED_DATA12 read_passphrase(void) {
  TPM_RESULT res;
  struct TPM_AUTHDATA_option nv_auth;
# 136 "/Users/scottconstable/Documents/SU_Graduate/SABLE/sable/src/sable_verified.c"
  nv_auth.hasValue = 0;
  res = TPM_NV_ReadValue(pp_blob, 4, 0, sizeof(pp_blob), nv_auth, 0);
  { if (res) { ; exit(res); } };


  return unpack_TPM_STORED_DATA12(pp_blob, sizeof(pp_blob));
}

void unseal_passphrase(TPM_AUTHDATA srk_auth, TPM_AUTHDATA pp_auth,
                       TPM_STORED_DATA12 sealed_pp) {
  TPM_RESULT res;

  res = TPM_OIAP(&srk_session);
  { if (res) { ; exit(res); } };

  res = TPM_OIAP(&pp_session);
  { if (res) { ; exit(res); } };

  res = TPM_Unseal(sealed_pp, (BYTE *)passphrase, sizeof(passphrase), ((UINT32)0x40000000),
                   srk_auth, &srk_session, pp_auth, &pp_session);
  { if (res) { ; exit(res); } };
}

void trusted_boot(void) {
  TPM_STORED_DATA12 sealed_pp = read_passphrase();



  TPM_AUTHDATA pp_auth = get_authdata();


  TPM_AUTHDATA srk_auth = get_authdata();

  unseal_passphrase(srk_auth, pp_auth, sealed_pp);
# 211 "/Users/scottconstable/Documents/SU_Graduate/SABLE/sable/src/sable_verified.c"
}
