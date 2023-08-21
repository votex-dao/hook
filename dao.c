#include <stdint.h>
#include "hookapi.h"

#define MAX_MEMO_SIZE 4096
#define MINIMUM_FUTURE_LEDGER 60

int64_t hook(uint32_t reserved) {
    unsigned char dao_accid[20];
    hook_account((uint32_t)dao_accid, 20);

    etxn_reserve(1);

    uint8_t origin_account[20];
    int32_t origin_account_len = otxn_field(SBUF(origin_account), sfAccount);
    if (origin_account_len < 20)
        rollback(SBUF("Dao: sfAccount field missing!!!"), 10);

    int equal = 0;
    BUFFER_EQUAL(equal, dao_accid, origin_account, 20);
    if (equal)
        accept(SBUF("Dao: Outgoing transaction"), 20);

    uint8_t tx_blob[MAX_MEMO_SIZE];
    int64_t tx_len = 0;
    uint8_t endorsement_id[32];

    int64_t endorsement_id_len = otxn_field(SBUF(endorsement_id), sfInvoiceID);

    if (endorsement_id_len == 32) {
        endorsement_id[31] = (endorsement_id[31] & 0xF0U) + 0x0FU;
        tx_len = state(SBUF(tx_blob), SBUF(endorsement_id));
        if (tx_len < 0)
            rollback(SBUF("Dao: Received endorsement id that did not correspond to a submitted multisig txn."), 1);

        int64_t lls_lookup = sto_subfield(tx_blob, tx_len, sfLastLedgerSequence);
        uint8_t* lls_ptr = SUB_OFFSET(lls_lookup) + tx_blob;
        uint32_t lls_len = SUB_LENGTH(lls_lookup);

        if (lls_len != 4 || UINT32_FROM_BUF(lls_ptr) < ledger_seq()) {
            if (state_set(0, 0, SBUF(endorsement_id)) < 0)
                rollback(SBUF("Dao: Error erasing old txn blob."), 40);

            accept(SBUF("Dao: Multisig txn was too old (last ledger seq passed) and was erased."), 1);
        }
    }

    uint8_t memos[MAX_MEMO_SIZE];
    int64_t memos_len = otxn_field(SBUF(memos), sfMemos);

    uint32_t payload_len = 0;
    uint8_t* payload_ptr = 0;

    if (memos_len <= 0 && endorsement_id_len <= 0)
        accept(SBUF("Dao: Incoming txn with neither memo nor endorsement ID, passing."), 0);

    if (memos_len > 0 && endorsement_id_len > 0)
        rollback(SBUF("Dao: Incoming txn with both memo and endorsement ID, abort."), 0);

    uint8_t keylet[34];
    CLEARBUF(keylet);
    if (util_keylet(SBUF(keylet), KEYLET_SIGNERS, SBUF(dao_accid), 0, 0, 0, 0) != 34)
        rollback(SBUF("Dao: Internal error, could not generate keylet"), 10);

    int64_t slot_num = slot_set(SBUF(keylet), 0);
    TRACEVAR(slot_num);
    if (slot_num < 0)
        rollback(SBUF("Dao: Could not set keylet in slot"), 10);

    int64_t signer_quorum = slot_subfield(slot_num, sfSignerQuorum, 0);
    if (signer_quorum < 0)
        rollback(SBUF("Dao: Could not find sfSignerQuorum on hook account"), 20);

    uint32_t signer_quorum_val = 0;
    uint8_t buf[4];
    signer_quorum = slot(SBUF(buf), signer_quorum);
    if (signer_quorum != 4)
        rollback(SBUF("Dao: Could not fetch sfSignerQuorum from sfSignerEntries."), 80);

    signer_quorum_val = UINT32_FROM_BUF(buf);
    TRACEVAR(signer_quorum_val);

    int64_t signer_entries = slot_subfield(slot_num, sfSignerEntries, slot_num);
    if (signer_entries < 0)
        rollback(SBUF("Dao: Could not find sfSignerEntries on hook account"), 20);

    int64_t signer_count = slot_count(slot_num);
    if (signer_count < 0)
        rollback(SBUF("Dao: Could not fetch sfSignerEntries count"), 30);

    int subslot = 0;
    uint8_t found = 0;
    uint16_t signer_weight = 0;

    for (int i = 0; GUARD(8), i < signer_count + 1; ++i) {
        subslot = slot_subarray(slot_num, i, subslot);
        if (subslot < 0)
            rollback(SBUF("Dao: Could not fetch one of the sfSigner entries [subarray]."), 40);

        result = slot_subfield(subslot, sfAccount, 0);
        if (result < 0)
            rollback(SBUF("Dao: Could not fetch one of the account entries in sfSigner."), 50);

        uint8_t signer_account[20];
        result = slot(SBUF(signer_account), result);
        if (result != 20)
            rollback(SBUF("Dao: Could not fetch one of the sfSigner entries [slot sfAccount]."), 60);

        result = slot_subfield(subslot, sfSignerWeight, 0);
        if (result < 0)
            rollback(SBUF("Dao: Could not fetch sfSignerWeight from sfSignerEntry."), 70);

        result = slot(buf, 2, result);

        if (result != 2)
            rollback(SBUF("Dao: Could not fetch sfSignerWeight from sfSignerEntry."), 80);

        signer_weight = UINT16_FROM_BUF(buf);

        TRACEVAR(signer_weight);
        TRACEHEX(origin_account);
        TRACEHEX(signer_account);

        int equal = 0;
        BUFFER_EQUAL_GUARD(equal, signer_account, 20, origin_account, 20, 8);
        if (equal) {
            found = i + 1;
            break;
        }
    }

    if (!found)
        rollback(SBUF("Dao: Your account was not present in the signer list."), 70);

    if (memos_len > 0) {
        if (endorsement_id_len > 0)
            rollback(SBUF("Dao: Incoming transaction with both endorsement id and memo. Aborting."), 0);

        int64_t memo_lookup = sto_subarray(memos, memos_len, 0);
        uint8_t* memo_ptr = SUB_OFFSET(memo_lookup) + memos;
        uint32_t memo_len = SUB_LENGTH(memo_lookup);

        memo_lookup = sto_subfield(memo_ptr, memo_len, sfMemo);
        memo_ptr = SUB_OFFSET(memo_lookup) + memo_ptr;
        memo_len = SUB_LENGTH(memo_lookup);

        if (memo_lookup < 0)
            rollback(SBUF("Dao: Incoming txn had a blank sfMemos, abort."), 1);

        int64_t format_lookup = sto_subfield(memo_ptr, memo_len, sfMemoFormat);
        uint8_t* format_ptr = SUB_OFFSET(format_lookup) + memo_ptr;
        uint32_t format_len = SUB_LENGTH(format_lookup);

        int is_unsigned_payload = 0;
        BUFFER_EQUAL_STR_GUARD(is_unsigned_payload, format_ptr, format_len, "unsigned/payload+1", 1);
        if (!is_unsigned_payload)
            accept(SBUF("Dao: Memo is an invalid format. Passing txn."), 50);

        int64_t data_lookup = sto_subfield(memo_ptr, memo_len, sfMemoData);
        uint8_t* data_ptr = SUB_OFFSET(data_lookup) + memo_ptr;
        uint32_t data_len = SUB_LENGTH(data_lookup);

        if (data_len > MAX_MEMO_SIZE)
            rollback(SBUF("Dao: Memo too large (4kib max)."), 4);

        int64_t txtype_lookup = sto_subfield(data_ptr, data_len, sfTransactionType);
        if (txtype_lookup < 0)
            rollback(SBUF("Dao: Memo is invalid format. Should be an unsigned transaction."), 2);

        int64_t lls_lookup = sto_subfield(data_ptr, data_len, sfLastLedgerSequence);
        uint8_t* lls_ptr = SUB_OFFSET(lls_lookup) + data_ptr;
        uint32_t lls_len = SUB_LENGTH(lls_lookup);

        if (lls_len != 4 || UINT32_FROM_BUF(lls_ptr) < ledger_seq() + MINIMUM_FUTURE_LEDGER)
            rollback(SBUF("Dao: Provided txn blob expires too soon (LastLedgerSeq)."), 3);

        if (util_sha512h(SBUF(endorsement_id), data_ptr, data_len) < 0)
            rollback(SBUF("Dao: Could not compute sha512 over the submitted txn."), 5);

        TRACEHEX(endorsement_id);

        endorsement_id[31] = (endorsement_id[31] & 0xF0U) + 0x0FU;

        int64_t ssrv = state_set(data_ptr, data_len, SBUF(endorsement_id));
        if (ssrv < 0) {
            TRACEVAR(ssrv);
            rollback(SBUF("Dao: Could not write txn to hook state."), 6);
        }
    }

    endorsement_id[31] = (endorsement_id[31] & 0xF0U) + found;

    UINT16_TO_BUF(buf, signer_weight);
    if (state_set(buf, 2, SBUF(endorsement_id)) != 2)
        rollback(SBUF("Dao: Could not write signature to hook state."), 7);

    uint32_t total = 0;
    for (uint8_t i = 1; GUARD(8), i < 9; ++i) {
        endorsement_id[31] = (endorsement_id[31] & 0xF0U) + i;
        if (state(buf, 2, SBUF(endorsement_id)) == 2)
            total += UINT16_FROM_BUF(buf);
    }

    TRACEVAR(total);
    TRACEVAR(signer_quorum_val);

    if (total < signer_quorum_val) {
        uint8_t header[] = "Dao: Accepted waiting for other signers...: ";
        uint8_t returnval[112];
        uint8_t* ptr = returnval;
        for (int i = 0; GUARD(47), i < 47; ++i)
            *ptr++ = header[i];
        for (int i = 0; GUARD(32), i < 32; ++i) {
            uint8_t hi = (endorsement_id[i] >> 4U);
            uint8_t lo = (endorsement_id[i] & 0xFU);

            hi += (hi > 9 ? ('A'-10) : '0');
            lo += (lo > 9 ? ('A'-10) : '0');
            *ptr++ = hi;
            *ptr++ = lo;
        }
        accept(SBUF(returnval), 0);
    }

    int should_emit = 1;
    endorsement_id[31] = (endorsement_id[31] & 0xF0U) + 0x0FU;
    tx_len = state(SBUF(tx_blob), SBUF(endorsement_id));
    if (tx_len < 0)
        should_emit = 0;

    state_set(0, 0, SBUF(endorsement_id));
    for (uint8_t i = 1; GUARD(8), i < 9; ++i) {
        endorsement_id[31] = (endorsement_id[31] & 0xF0U) + i;
        state_set(0, 0, SBUF(endorsement_id));
    }

    if (!should_emit)
        rollback(SBUF("Dao: Tried to emit multisig txn but it was missing"), 1);

    int64_t lls_lookup = sto_subfield(tx_blob, tx_len, sfLastLedgerSequence);
    uint8_t* lls_ptr = SUB_OFFSET(lls_lookup) + tx_blob;
    uint32_t lls_len = SUB_LENGTH(lls_lookup);
    if (lls_len != 4)
        rollback(SBUF("Dao: Was about to emit txn but it doesn't have LastLedgerSequence"), 1);

    uint32_t lls_old = UINT32_FROM_BUF(lls_ptr);
    if (lls_old < ledger_seq())
        rollback(SBUF("Dao: Was about to emit txn but it's too old now"), 1);

    uint8_t buffer[MAX_MEMO_SIZE];
    uint8_t* buffer2 = buffer;
    uint8_t* buffer1 = tx_blob;

    result = sto_erase(buffer2, MAX_MEMO_SIZE, buffer1, tx_len, sfSigners);
    if (result > 0)
        tx_len = result;
    else
        BUFFER_SWAP(buffer1, buffer2);

    uint8_t zeroed[6];
    CLEARBUF(zeroed);
    zeroed[0] = 0x24U;

    tx_len = sto_emplace(buffer1, MAX_MEMO_SIZE, buffer2, tx_len, zeroed, 5, sfSequence);
    if (tx_len <= 0)
        rollback(SBUF("Dao: Emplacing sfSequence failed."), 1);

    zeroed[0] = 0x74U;
    tx_len = sto_emplace(buffer2, MAX_MEMO_SIZE, buffer1, tx_len, zeroed, 2, sfTxnSignature);
    TRACEVAR(tx_len);
    if (tx_len <= 0)
        rollback(SBUF("Dao: Emplacing sfTxnSignature failed."), 1);

    zeroed[0] = 0x73U;
    tx_len = sto_emplace(buffer1, MAX_MEMO_SIZE, buffer2, tx_len, zeroed, 2, sfSigningPubKey);
    TRACEVAR(tx_len);
    if (tx_len <= 0)
        rollback(SBUF("Dao: Emplacing sfSigningPubKey failed."), 1);

    uint32_t fls = ledger_seq() + 1;
    zeroed[0] = 0x20U;
    zeroed[1] = 0x1AU;
    UINT32_TO_BUF(zeroed + 2, fls);
    tx_len = sto_emplace(buffer2, MAX_MEMO_SIZE, buffer1, tx_len, zeroed, 6, sfFirstLedgerSequence);

    if (tx_len <= 0)
        rollback(SBUF("Dao: Emplacing sfFirstLedgerSequence failed."), 1);

    uint32_t lls_new = fls + 4;
    if (lls_old > lls_new) {
        trace("fixing", 6, buffer2, tx_len, 1);

        tx_len = sto_erase(buffer1, MAX_MEMO_SIZE, buffer2, tx_len, sfLastLedgerSequence);
        if (tx_len <= 0)
            rollback(SBUF("Dao: Erasing sfLastLedgerSequence failed."), 1);

        zeroed[1] = 0x1BU;
        UINT32_TO_BUF(zeroed + 2, lls_new);
        tx_len = sto_emplace(buffer2, MAX_MEMO_SIZE, buffer1, tx_len, zeroed, 6, sfLastLedgerSequence);
        if (tx_len <= 0)
            rollback(SBUF("Dao: Emplacing sfLastLedgerSequence failed."), 1);
    }

    uint8_t emitdet[138];
    result = etxn_details(SBUF(emitdet));

    if (result < 0)
        rollback(SBUF("Dao: EmitDetails failed to generate."), 1);

    tx_len = sto_emplace(buffer1, MAX_MEMO_SIZE, buffer2, tx_len, emitdet, result, sfEmitDetails);
    if (tx_len < 0)
        rollback(SBUF("Dao: Emplacing sfEmitDetails failed."), 1);

    uint8_t fee[ENCODE_DROPS_SIZE];
    uint8_t* fee_ptr = fee;
    int64_t fee_to_pay = etxn_fee_base(buffer1, tx_len);
    if (fee_to_pay < 0)
        rollback(SBUF("Dao: Computing sfFee failed."), 1);

    ENCODE_DROPS(fee_ptr, fee_to_pay, amFEE);
    tx_len = sto_emplace(buffer2, MAX_MEMO_SIZE, buffer1, tx_len, SBUF(fee), sfFee);

    if (tx_len <= 0)
        rollback(SBUF("Dao: Emplacing sfFee failed."), 1);

    uint8_t emithash[32];
    int64_t erv = emit(SBUF(emithash), buffer2, tx_len);
    if (erv < 0) {
        TRACEVAR(erv);
        accept(SBUF("Dao: All conditions met but emission failed: proposed txn was malformed."), 1);
    }

    accept(SBUF("Dao: Emitted multisigned txn"), 0);
    return 0;
}
