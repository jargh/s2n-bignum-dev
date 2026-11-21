// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// The offsets and sizes of the kernel structures that the proofs and tests
// of the WireGuard image use, as "->NAME VALUE" lines in the assembly output
// (the method of the kernel's asm-offsets.c). gen_offsets.sh compiles this
// file exactly as Kbuild compiled noise.o, but to assembly.
// ----------------------------------------------------------------------------

#include "noise.h"
#include "peer.h"
#include "device.h"
#include "peerlookup.h"
#include "messages.h"
#include "cookie.h"
#include <crypto/blake2s.h>
#include <crypto/chacha.h>
#include <crypto/poly1305.h>
#include <linux/time64.h>

#define DEFINE(sym, val) asm volatile("\n->" #sym " %0" : : "i" (val))
#define OFFSET(sym, str, mem) DEFINE(sym, offsetof(struct str, mem))
#define SIZE(sym, str) DEFINE(sym, sizeof(struct str))

void wg_offsets(void);
void wg_offsets(void)
{
        SIZE(index_hashtable_entry_size, index_hashtable_entry);
        OFFSET(index_hashtable_entry_peer, index_hashtable_entry, peer);
        OFFSET(index_hashtable_entry_index_hash, index_hashtable_entry,
               index_hash);
        OFFSET(index_hashtable_entry_type, index_hashtable_entry, type);
        OFFSET(index_hashtable_entry_index, index_hashtable_entry, index);
        SIZE(index_hashtable_size, index_hashtable);
        OFFSET(index_hashtable_lock, index_hashtable, lock);

        SIZE(noise_handshake_size, noise_handshake);
        OFFSET(noise_handshake_entry, noise_handshake, entry);
        OFFSET(noise_handshake_state, noise_handshake, state);
        OFFSET(noise_handshake_last_initiation_consumption, noise_handshake,
               last_initiation_consumption);
        OFFSET(noise_handshake_static_identity, noise_handshake,
               static_identity);
        OFFSET(noise_handshake_ephemeral_private, noise_handshake,
               ephemeral_private);
        OFFSET(noise_handshake_remote_static, noise_handshake, remote_static);
        OFFSET(noise_handshake_remote_ephemeral, noise_handshake,
               remote_ephemeral);
        OFFSET(noise_handshake_precomputed_static_static, noise_handshake,
               precomputed_static_static);
        OFFSET(noise_handshake_preshared_key, noise_handshake, preshared_key);
        OFFSET(noise_handshake_hash, noise_handshake, hash);
        OFFSET(noise_handshake_chaining_key, noise_handshake, chaining_key);
        OFFSET(noise_handshake_latest_timestamp, noise_handshake,
               latest_timestamp);
        OFFSET(noise_handshake_remote_index, noise_handshake, remote_index);
        OFFSET(noise_handshake_lock, noise_handshake, lock);

        SIZE(noise_static_identity_size, noise_static_identity);
        OFFSET(noise_static_identity_static_public, noise_static_identity,
               static_public);
        OFFSET(noise_static_identity_static_private, noise_static_identity,
               static_private);
        OFFSET(noise_static_identity_lock, noise_static_identity, lock);
        OFFSET(noise_static_identity_has_identity, noise_static_identity,
               has_identity);

        SIZE(noise_symmetric_key_size, noise_symmetric_key);
        OFFSET(noise_symmetric_key_key, noise_symmetric_key, key);
        OFFSET(noise_symmetric_key_birthdate, noise_symmetric_key, birthdate);
        OFFSET(noise_symmetric_key_is_valid, noise_symmetric_key, is_valid);

        SIZE(noise_keypair_size, noise_keypair);
        OFFSET(noise_keypair_entry, noise_keypair, entry);
        OFFSET(noise_keypair_sending, noise_keypair, sending);
        OFFSET(noise_keypair_sending_counter, noise_keypair, sending_counter);
        OFFSET(noise_keypair_receiving, noise_keypair, receiving);
        OFFSET(noise_keypair_receiving_counter, noise_keypair,
               receiving_counter);
        OFFSET(noise_keypair_remote_index, noise_keypair, remote_index);
        OFFSET(noise_keypair_i_am_the_initiator, noise_keypair,
               i_am_the_initiator);
        OFFSET(noise_keypair_refcount, noise_keypair, refcount);
        OFFSET(noise_keypair_internal_id, noise_keypair, internal_id);

        SIZE(noise_keypairs_size, noise_keypairs);
        OFFSET(noise_keypairs_current_keypair, noise_keypairs,
               current_keypair);
        OFFSET(noise_keypairs_previous_keypair, noise_keypairs,
               previous_keypair);
        OFFSET(noise_keypairs_next_keypair, noise_keypairs, next_keypair);
        OFFSET(noise_keypairs_keypair_update_lock, noise_keypairs,
               keypair_update_lock);

        SIZE(wg_peer_size, wg_peer);
        OFFSET(wg_peer_device, wg_peer, device);
        OFFSET(wg_peer_handshake, wg_peer, handshake);
        OFFSET(wg_peer_keypairs, wg_peer, keypairs);
        OFFSET(wg_peer_is_dead, wg_peer, is_dead);
        OFFSET(wg_peer_internal_id, wg_peer, internal_id);
        OFFSET(wg_peer_refcount, wg_peer, refcount);
        OFFSET(wg_peer_latest_cookie, wg_peer, latest_cookie);

        SIZE(wg_device_size, wg_device);
        OFFSET(wg_device_dev, wg_device, dev);
        OFFSET(wg_device_static_identity, wg_device, static_identity);
        OFFSET(wg_device_index_hashtable, wg_device, index_hashtable);
        OFFSET(wg_device_peer_hashtable, wg_device, peer_hashtable);
        OFFSET(wg_device_cookie_checker, wg_device, cookie_checker);

        SIZE(blake2s_state_size, blake2s_state);
        OFFSET(blake2s_state_h, blake2s_state, h);
        OFFSET(blake2s_state_t, blake2s_state, t);
        OFFSET(blake2s_state_f, blake2s_state, f);
        OFFSET(blake2s_state_buf, blake2s_state, buf);
        OFFSET(blake2s_state_buflen, blake2s_state, buflen);
        OFFSET(blake2s_state_outlen, blake2s_state, outlen);

        SIZE(chacha_state_size, chacha_state);
        SIZE(poly1305_desc_ctx_size, poly1305_desc_ctx);
        OFFSET(poly1305_desc_ctx_buf, poly1305_desc_ctx, buf);
        OFFSET(poly1305_desc_ctx_buflen, poly1305_desc_ctx, buflen);
        OFFSET(poly1305_desc_ctx_s, poly1305_desc_ctx, s);
        OFFSET(poly1305_desc_ctx_state, poly1305_desc_ctx, state);
        SIZE(poly1305_block_state_size, poly1305_block_state);

        SIZE(message_handshake_initiation_size, message_handshake_initiation);
        OFFSET(message_handshake_initiation_sender_index,
               message_handshake_initiation, sender_index);
        OFFSET(message_handshake_initiation_unencrypted_ephemeral,
               message_handshake_initiation, unencrypted_ephemeral);
        OFFSET(message_handshake_initiation_encrypted_static,
               message_handshake_initiation, encrypted_static);
        OFFSET(message_handshake_initiation_encrypted_timestamp,
               message_handshake_initiation, encrypted_timestamp);
        OFFSET(message_handshake_initiation_macs,
               message_handshake_initiation, macs);
        SIZE(message_handshake_response_size, message_handshake_response);
        SIZE(message_handshake_cookie_size, message_handshake_cookie);
        OFFSET(message_handshake_cookie_receiver_index,
               message_handshake_cookie, receiver_index);
        OFFSET(message_handshake_cookie_nonce, message_handshake_cookie,
               nonce);
        OFFSET(message_handshake_cookie_encrypted_cookie,
               message_handshake_cookie, encrypted_cookie);
        SIZE(message_macs_size, message_macs);
        OFFSET(message_macs_mac1, message_macs, mac1);
        OFFSET(message_macs_mac2, message_macs, mac2);

        SIZE(cookie_checker_size, cookie_checker);
        OFFSET(cookie_checker_secret, cookie_checker, secret);
        OFFSET(cookie_checker_cookie_encryption_key, cookie_checker,
               cookie_encryption_key);
        OFFSET(cookie_checker_message_mac1_key, cookie_checker,
               message_mac1_key);
        OFFSET(cookie_checker_secret_birthdate, cookie_checker,
               secret_birthdate);
        OFFSET(cookie_checker_secret_lock, cookie_checker, secret_lock);
        OFFSET(cookie_checker_device, cookie_checker, device);
        SIZE(cookie_size, cookie);
        OFFSET(cookie_birthdate, cookie, birthdate);
        OFFSET(cookie_is_valid, cookie, is_valid);
        OFFSET(cookie_cookie, cookie, cookie);
        OFFSET(cookie_have_sent_mac1, cookie, have_sent_mac1);
        OFFSET(cookie_last_mac1_sent, cookie, last_mac1_sent);
        OFFSET(cookie_cookie_decryption_key, cookie, cookie_decryption_key);
        OFFSET(cookie_message_mac1_key, cookie, message_mac1_key);
        OFFSET(cookie_lock, cookie, lock);

        OFFSET(sk_buff_len, sk_buff, len);
        OFFSET(sk_buff_protocol, sk_buff, protocol);
        OFFSET(sk_buff_transport_header, sk_buff, transport_header);
        OFFSET(sk_buff_network_header, sk_buff, network_header);
        OFFSET(sk_buff_head, sk_buff, head);
        OFFSET(sk_buff_data, sk_buff, data);
        SIZE(rw_semaphore_size, rw_semaphore);
        SIZE(timespec64_size, timespec64);
        OFFSET(timespec64_tv_sec, timespec64, tv_sec);
        OFFSET(timespec64_tv_nsec, timespec64, tv_nsec);
}
