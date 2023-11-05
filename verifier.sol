// SPDX-License-Identifier: MIT

pragma solidity ^0.8.0;

contract Halo2Verifier {
    uint256 internal constant    PROOF_LEN_CPTR = 0x44;
    uint256 internal constant        PROOF_CPTR = 0x64;
    uint256 internal constant NUM_INSTANCE_CPTR = 0x3324;
    uint256 internal constant     INSTANCE_CPTR = 0x3344;

    uint256 internal constant FIRST_QUOTIENT_X_CPTR = 0x1464;
    uint256 internal constant  LAST_QUOTIENT_X_CPTR = 0x1524;

    uint256 internal constant                VK_MPTR = 0x1d60;
    uint256 internal constant         VK_DIGEST_MPTR = 0x1d60;
    uint256 internal constant                 K_MPTR = 0x1d80;
    uint256 internal constant             N_INV_MPTR = 0x1da0;
    uint256 internal constant             OMEGA_MPTR = 0x1dc0;
    uint256 internal constant         OMEGA_INV_MPTR = 0x1de0;
    uint256 internal constant    OMEGA_INV_TO_L_MPTR = 0x1e00;
    uint256 internal constant     NUM_INSTANCES_MPTR = 0x1e20;
    uint256 internal constant   HAS_ACCUMULATOR_MPTR = 0x1e40;
    uint256 internal constant        ACC_OFFSET_MPTR = 0x1e60;
    uint256 internal constant     NUM_ACC_LIMBS_MPTR = 0x1e80;
    uint256 internal constant NUM_ACC_LIMB_BITS_MPTR = 0x1ea0;
    uint256 internal constant              G1_X_MPTR = 0x1ec0;
    uint256 internal constant              G1_Y_MPTR = 0x1ee0;
    uint256 internal constant            G2_X_1_MPTR = 0x1f00;
    uint256 internal constant            G2_X_2_MPTR = 0x1f20;
    uint256 internal constant            G2_Y_1_MPTR = 0x1f40;
    uint256 internal constant            G2_Y_2_MPTR = 0x1f60;
    uint256 internal constant      NEG_S_G2_X_1_MPTR = 0x1f80;
    uint256 internal constant      NEG_S_G2_X_2_MPTR = 0x1fa0;
    uint256 internal constant      NEG_S_G2_Y_1_MPTR = 0x1fc0;
    uint256 internal constant      NEG_S_G2_Y_2_MPTR = 0x1fe0;

    uint256 internal constant CHALLENGE_MPTR = 0x3940;

    uint256 internal constant THETA_MPTR = 0x3940;
    uint256 internal constant  BETA_MPTR = 0x3960;
    uint256 internal constant GAMMA_MPTR = 0x3980;
    uint256 internal constant     Y_MPTR = 0x39a0;
    uint256 internal constant     X_MPTR = 0x39c0;
    uint256 internal constant  ZETA_MPTR = 0x39e0;
    uint256 internal constant    NU_MPTR = 0x3a00;
    uint256 internal constant    MU_MPTR = 0x3a20;

    uint256 internal constant       ACC_LHS_X_MPTR = 0x3a40;
    uint256 internal constant       ACC_LHS_Y_MPTR = 0x3a60;
    uint256 internal constant       ACC_RHS_X_MPTR = 0x3a80;
    uint256 internal constant       ACC_RHS_Y_MPTR = 0x3aa0;
    uint256 internal constant             X_N_MPTR = 0x3ac0;
    uint256 internal constant X_N_MINUS_1_INV_MPTR = 0x3ae0;
    uint256 internal constant          L_LAST_MPTR = 0x3b00;
    uint256 internal constant         L_BLIND_MPTR = 0x3b20;
    uint256 internal constant             L_0_MPTR = 0x3b40;
    uint256 internal constant   INSTANCE_EVAL_MPTR = 0x3b60;
    uint256 internal constant   QUOTIENT_EVAL_MPTR = 0x3b80;
    uint256 internal constant      QUOTIENT_X_MPTR = 0x3ba0;
    uint256 internal constant      QUOTIENT_Y_MPTR = 0x3bc0;
    uint256 internal constant          R_EVAL_MPTR = 0x3be0;
    uint256 internal constant   PAIRING_LHS_X_MPTR = 0x3c00;
    uint256 internal constant   PAIRING_LHS_Y_MPTR = 0x3c20;
    uint256 internal constant   PAIRING_RHS_X_MPTR = 0x3c40;
    uint256 internal constant   PAIRING_RHS_Y_MPTR = 0x3c60;

    function verifyProof(
        bytes calldata proof,
        uint256[] calldata instances
    ) public returns (bool) {
        assembly {
            // Read EC point (x, y) at (proof_cptr, proof_cptr + 0x20),
            // and check if the point is on affine plane,
            // and store them in (hash_mptr, hash_mptr + 0x20).
            // Return updated (success, proof_cptr, hash_mptr).
            function read_ec_point(success, proof_cptr, hash_mptr, q) -> ret0, ret1, ret2 {
                let x := calldataload(proof_cptr)
                let y := calldataload(add(proof_cptr, 0x20))
                ret0 := and(success, lt(x, q))
                ret0 := and(ret0, lt(y, q))
                ret0 := and(ret0, eq(mulmod(y, y, q), addmod(mulmod(x, mulmod(x, x, q), q), 3, q)))
                mstore(hash_mptr, x)
                mstore(add(hash_mptr, 0x20), y)
                ret1 := add(proof_cptr, 0x40)
                ret2 := add(hash_mptr, 0x40)
            }

            // Squeeze challenge by keccak256(memory[0..hash_mptr]),
            // and store hash mod r as challenge in challenge_mptr,
            // and push back hash in 0x00 as the first input for next squeeze.
            // Return updated (challenge_mptr, hash_mptr).
            function squeeze_challenge(challenge_mptr, hash_mptr, r) -> ret0, ret1 {
                let hash := keccak256(0x00, hash_mptr)
                mstore(challenge_mptr, mod(hash, r))
                mstore(0x00, hash)
                ret0 := add(challenge_mptr, 0x20)
                ret1 := 0x20
            }

            // Squeeze challenge without absorbing new input from calldata,
            // by putting an extra 0x01 in memory[0x20] and squeeze by keccak256(memory[0..21]),
            // and store hash mod r as challenge in challenge_mptr,
            // and push back hash in 0x00 as the first input for next squeeze.
            // Return updated (challenge_mptr).
            function squeeze_challenge_cont(challenge_mptr, r) -> ret {
                mstore8(0x20, 0x01)
                let hash := keccak256(0x00, 0x21)
                mstore(challenge_mptr, mod(hash, r))
                mstore(0x00, hash)
                ret := add(challenge_mptr, 0x20)
            }

            // Batch invert values in memory[mptr_start..mptr_end] in place.
            // Return updated (success).
            function batch_invert(success, mptr_start, mptr_end, r) -> ret {
                let gp_mptr := mptr_end
                let gp := mload(mptr_start)
                let mptr := add(mptr_start, 0x20)
                for
                    {}
                    lt(mptr, sub(mptr_end, 0x20))
                    {}
                {
                    gp := mulmod(gp, mload(mptr), r)
                    mstore(gp_mptr, gp)
                    mptr := add(mptr, 0x20)
                    gp_mptr := add(gp_mptr, 0x20)
                }
                gp := mulmod(gp, mload(mptr), r)

                mstore(gp_mptr, 0x20)
                mstore(add(gp_mptr, 0x20), 0x20)
                mstore(add(gp_mptr, 0x40), 0x20)
                mstore(add(gp_mptr, 0x60), gp)
                mstore(add(gp_mptr, 0x80), sub(r, 2))
                mstore(add(gp_mptr, 0xa0), r)
                ret := and(success, staticcall(gas(), 0x05, gp_mptr, 0xc0, gp_mptr, 0x20))
                let all_inv := mload(gp_mptr)

                let first_mptr := mptr_start
                let second_mptr := add(first_mptr, 0x20)
                gp_mptr := sub(gp_mptr, 0x20)
                for
                    {}
                    lt(second_mptr, mptr)
                    {}
                {
                    let inv := mulmod(all_inv, mload(gp_mptr), r)
                    all_inv := mulmod(all_inv, mload(mptr), r)
                    mstore(mptr, inv)
                    mptr := sub(mptr, 0x20)
                    gp_mptr := sub(gp_mptr, 0x20)
                }
                let inv_first := mulmod(all_inv, mload(second_mptr), r)
                let inv_second := mulmod(all_inv, mload(first_mptr), r)
                mstore(first_mptr, inv_first)
                mstore(second_mptr, inv_second)
            }

            // Add (x, y) into point at (0x00, 0x20).
            // Return updated (success).
            function ec_add_acc(success, x, y) -> ret {
                mstore(0x40, x)
                mstore(0x60, y)
                ret := and(success, staticcall(gas(), 0x06, 0x00, 0x80, 0x00, 0x40))
            }

            // Scale point at (0x00, 0x20) by scalar.
            function ec_mul_acc(success, scalar) -> ret {
                mstore(0x40, scalar)
                ret := and(success, staticcall(gas(), 0x07, 0x00, 0x60, 0x00, 0x40))
            }

            // Add (x, y) into point at (0x80, 0xa0).
            // Return updated (success).
            function ec_add_tmp(success, x, y) -> ret {
                mstore(0xc0, x)
                mstore(0xe0, y)
                ret := and(success, staticcall(gas(), 0x06, 0x80, 0x80, 0x80, 0x40))
            }

            // Scale point at (0x80, 0xa0) by scalar.
            // Return updated (success).
            function ec_mul_tmp(success, scalar) -> ret {
                mstore(0xc0, scalar)
                ret := and(success, staticcall(gas(), 0x07, 0x80, 0x60, 0x80, 0x40))
            }

            // Perform pairing check.
            // Return updated (success).
            function ec_pairing(success, lhs_x, lhs_y, rhs_x, rhs_y) -> ret {
                mstore(0x00, lhs_x)
                mstore(0x20, lhs_y)
                mstore(0x40, mload(G2_X_1_MPTR))
                mstore(0x60, mload(G2_X_2_MPTR))
                mstore(0x80, mload(G2_Y_1_MPTR))
                mstore(0xa0, mload(G2_Y_2_MPTR))
                mstore(0xc0, rhs_x)
                mstore(0xe0, rhs_y)
                mstore(0x100, mload(NEG_S_G2_X_1_MPTR))
                mstore(0x120, mload(NEG_S_G2_X_2_MPTR))
                mstore(0x140, mload(NEG_S_G2_Y_1_MPTR))
                mstore(0x160, mload(NEG_S_G2_Y_2_MPTR))
                ret := and(success, staticcall(gas(), 0x08, 0x00, 0x180, 0x00, 0x20))
                ret := and(ret, mload(0x00))
            }

            // Modulus
            let q := 21888242871839275222246405745257275088696311157297823662689037894645226208583 // BN254 base field
            let r := 21888242871839275222246405745257275088548364400416034343698204186575808495617 // BN254 scalar field

            // Initialize success as true
            let success := true

            {
                // Load vk into memory
                mstore(0x1d60, 0x2a6912de77bef8d5750d1c041b5831aba8a2b1af781f80376a3b4bc2338573de) // vk_digest
                mstore(0x1d80, 0x000000000000000000000000000000000000000000000000000000000000000d) // k
                mstore(0x1da0, 0x3062cb506d9a969cb702833453cd4c52654aa6a93775a2c5bf57d68443608001) // n_inv
                mstore(0x1dc0, 0x10e3d295c1599ff535a1bb49f23d81aa03bd0ed25881f9ed12b179af67f67ae1) // omega
                mstore(0x1de0, 0x09ff38534bd08f2b08b6010aaee9ac485d3afb3a9ae4280907537b08fc6e53e5) // omega_inv
                mstore(0x1e00, 0x1fe62c4a3c6640bbac666390d8ab7318a0de5374d46b2921e3217838d26470ad) // omega_inv_to_l
                mstore(0x1e20, 0x000000000000000000000000000000000000000000000000000000000000000a) // num_instances
                mstore(0x1e40, 0x0000000000000000000000000000000000000000000000000000000000000000) // has_accumulator
                mstore(0x1e60, 0x0000000000000000000000000000000000000000000000000000000000000000) // acc_offset
                mstore(0x1e80, 0x0000000000000000000000000000000000000000000000000000000000000000) // num_acc_limbs
                mstore(0x1ea0, 0x0000000000000000000000000000000000000000000000000000000000000000) // num_acc_limb_bits
                mstore(0x1ec0, 0x0000000000000000000000000000000000000000000000000000000000000001) // g1_x
                mstore(0x1ee0, 0x0000000000000000000000000000000000000000000000000000000000000002) // g1_y
                mstore(0x1f00, 0x198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c2) // g2_x_1
                mstore(0x1f20, 0x1800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed) // g2_x_2
                mstore(0x1f40, 0x090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b) // g2_y_1
                mstore(0x1f60, 0x12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa) // g2_y_2
                mstore(0x1f80, 0x186282957db913abd99f91db59fe69922e95040603ef44c0bd7aa3adeef8f5ac) // neg_s_g2_x_1
                mstore(0x1fa0, 0x17944351223333f260ddc3b4af45191b856689eda9eab5cbcddbbe570ce860d2) // neg_s_g2_x_2
                mstore(0x1fc0, 0x06d971ff4a7467c3ec596ed6efc674572e32fd6f52b721f97e35b0b3d3546753) // neg_s_g2_y_1
                mstore(0x1fe0, 0x06ecdb9f9567f59ed2eee36e1e1d58797fd13cc97fafc2910f5e8a12f202fa9a) // neg_s_g2_y_2
                mstore(0x2000, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[0].x
                mstore(0x2020, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[0].y
                mstore(0x2040, 0x2d27e7fc52668530dfbf7cbd5169f49efd29e4dd2f1eb2e2875fef2515882858) // fixed_comms[1].x
                mstore(0x2060, 0x0652057354ee41e1da8ebc0f2a3c1d5878cb3bd481bdfac31ab02d9d60c13441) // fixed_comms[1].y
                mstore(0x2080, 0x04ad7b516d9ecee781dd5ae088e1cdf69bcf721b249daf519b038912ea6b5f68) // fixed_comms[2].x
                mstore(0x20a0, 0x0e5ce3384d0dd885e61f8d1dc3b83bf3259e79fe87c6e8dea88618beec771774) // fixed_comms[2].y
                mstore(0x20c0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[3].x
                mstore(0x20e0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[3].y
                mstore(0x2100, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[4].x
                mstore(0x2120, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[4].y
                mstore(0x2140, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[5].x
                mstore(0x2160, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[5].y
                mstore(0x2180, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[6].x
                mstore(0x21a0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[6].y
                mstore(0x21c0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[7].x
                mstore(0x21e0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[7].y
                mstore(0x2200, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[8].x
                mstore(0x2220, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[8].y
                mstore(0x2240, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[9].x
                mstore(0x2260, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[9].y
                mstore(0x2280, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[10].x
                mstore(0x22a0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[10].y
                mstore(0x22c0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[11].x
                mstore(0x22e0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[11].y
                mstore(0x2300, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[12].x
                mstore(0x2320, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[12].y
                mstore(0x2340, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[13].x
                mstore(0x2360, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[13].y
                mstore(0x2380, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[14].x
                mstore(0x23a0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[14].y
                mstore(0x23c0, 0x206d343b875e8faae0f0d5d15aa33f02d3db687bf500e0375f4e52f0e6f00fdb) // fixed_comms[15].x
                mstore(0x23e0, 0x2469d1151c398c76264b69bdf1479f0388dede9090525dbe59b4d978ee881179) // fixed_comms[15].y
                mstore(0x2400, 0x107e9435cfac43e935318cc256d06b54556fe2df7452c8884b20d91702541557) // fixed_comms[16].x
                mstore(0x2420, 0x16597ebaf47e3cbc17e516a451ba34f65a7a63d8708f0a1e5d34a5d64bf1bc09) // fixed_comms[16].y
                mstore(0x2440, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[17].x
                mstore(0x2460, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[17].y
                mstore(0x2480, 0x0802c39db954e15f96d910e0c0c71158c815f83b2859249be299d7d7363cdba9) // fixed_comms[18].x
                mstore(0x24a0, 0x0c3f2384158442782822bed055d60596e2847199269be9aefaa3c9cf13ae47ab) // fixed_comms[18].y
                mstore(0x24c0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[19].x
                mstore(0x24e0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[19].y
                mstore(0x2500, 0x0a3e441354097257b00a2caa3d6137fab599462527c8668fea07846e931144b3) // fixed_comms[20].x
                mstore(0x2520, 0x07ed5c0456ed4044c722dba967f25d8e7a59c4e40f62e4dd35d01f13e7ce3f2c) // fixed_comms[20].y
                mstore(0x2540, 0x077718373c6f7db874748a044ee023dcd8f4fac0dca0a6d935c3fecf8c9c9816) // fixed_comms[21].x
                mstore(0x2560, 0x0b57274551f04b24f91f4d1fe4c47ce9af7a7af2dc8b35313017fd90a20bf270) // fixed_comms[21].y
                mstore(0x2580, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[22].x
                mstore(0x25a0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[22].y
                mstore(0x25c0, 0x0cb3560b4bde8db5d8b35dfc613740bfca343f1dc4c67e2458fb8c7c342e072f) // fixed_comms[23].x
                mstore(0x25e0, 0x2a793cfddfd3f8e64475ba21862addd9bc746b87db3a48e6c5946ca6f21ea91f) // fixed_comms[23].y
                mstore(0x2600, 0x2b7051b033ffb52842e7e20f5dfccfc21229d68b56ed7a2af54af05d852896bf) // fixed_comms[24].x
                mstore(0x2620, 0x2c783d6c01cb3c54515d5e9b8c3245622377678b66daac1b612cc733217bb99b) // fixed_comms[24].y
                mstore(0x2640, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[25].x
                mstore(0x2660, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[25].y
                mstore(0x2680, 0x19ab2de38553c54f639a943bb836910f91ae5ddf5cb7c5f6e686fbd0be9a0a4f) // fixed_comms[26].x
                mstore(0x26a0, 0x19a83dbc4471942311cbed40d3a2bf4a45a5553393c76eea26ce0dd546b34183) // fixed_comms[26].y
                mstore(0x26c0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[27].x
                mstore(0x26e0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[27].y
                mstore(0x2700, 0x021d5aea18fc33beeaf3d3285ae3c9e5ca2324d705d8aa32d30591f8d03835ba) // fixed_comms[28].x
                mstore(0x2720, 0x2f3e28537c5e1da2dc233627a1ac3b44d8b2af578cd1488f9ba4c79f190fd483) // fixed_comms[28].y
                mstore(0x2740, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[29].x
                mstore(0x2760, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[29].y
                mstore(0x2780, 0x09312ea3723422f77aaa5b9e93538358a17a88cb889a4fd0db31acb4109cd68f) // fixed_comms[30].x
                mstore(0x27a0, 0x23685f4a5a98fa8a898d30848df3d475e45cdfbd4865d3ed2031e084abd6366f) // fixed_comms[30].y
                mstore(0x27c0, 0x143e3cddf0010b5c4c20800123e8516f2ed06285b2d55dfb10de63830b840121) // fixed_comms[31].x
                mstore(0x27e0, 0x177a6275aca8fd138a876343da841617fcf32498802610b975fb443c1c446f2b) // fixed_comms[31].y
                mstore(0x2800, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[32].x
                mstore(0x2820, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[32].y
                mstore(0x2840, 0x03f3b20a3aeb116e35cd72378fb782835add76b924bc8e953cad1e1abd534d7c) // fixed_comms[33].x
                mstore(0x2860, 0x07afe239f37d8381a20a2dc7d20ff3c2d00375b0eff685c0c90d6965a7be46cf) // fixed_comms[33].y
                mstore(0x2880, 0x0dc7d116730b051d00ae67abc75b3a8d31ac1d3a0576e981085efb8ed65ab446) // fixed_comms[34].x
                mstore(0x28a0, 0x176b0e01b3f5ceba1909b46387959f9524fe7e69f82545ed4a4041a999a673c6) // fixed_comms[34].y
                mstore(0x28c0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[35].x
                mstore(0x28e0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[35].y
                mstore(0x2900, 0x2cfb049173f286a1b644c31391544133246841fdad917323c180800372f14aea) // fixed_comms[36].x
                mstore(0x2920, 0x091d0e6fcb030b7ca82f2a836fa9307e5d8d64b1f707927eb9df3c85f276b53e) // fixed_comms[36].y
                mstore(0x2940, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[37].x
                mstore(0x2960, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[37].y
                mstore(0x2980, 0x1a148662d9b4d58e8a3a57b9c6ce343f1a7226e571ba399ad484ce8a233f75bb) // fixed_comms[38].x
                mstore(0x29a0, 0x12ee5c849893f634893e300870c95c2f6c092311119e11b61a6ea0089c0a5b5e) // fixed_comms[38].y
                mstore(0x29c0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[39].x
                mstore(0x29e0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[39].y
                mstore(0x2a00, 0x0d720443d339c4be1ed49f1888b1376daaf628822ce44596f5cf2a52dbc30bed) // fixed_comms[40].x
                mstore(0x2a20, 0x2a7be25fb43e3fac65b34be26a409810d72db30309117cafa4d18a1c9ffe5085) // fixed_comms[40].y
                mstore(0x2a40, 0x2812edd4786782f80baeb25b7cf993a313f41763b3ed77e789d6fac7d2852cd3) // fixed_comms[41].x
                mstore(0x2a60, 0x0f0ef3fabb49cca51e472eb8194a28fc7640d277ad01a3d1af30208767968070) // fixed_comms[41].y
                mstore(0x2a80, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[42].x
                mstore(0x2aa0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[42].y
                mstore(0x2ac0, 0x088af5b3bc2d0fbab2e02a23def7035a058f6f82243ab49995619203ca328d16) // fixed_comms[43].x
                mstore(0x2ae0, 0x2f3313f7b2eb49c17bc7fbd53dba447dcbff86aedcf874dd68d05385e0ccb85e) // fixed_comms[43].y
                mstore(0x2b00, 0x1cf8fcf6e67cc288da83b31dcdc1ffec7fb9c63938edb7ed335fc4631f285321) // fixed_comms[44].x
                mstore(0x2b20, 0x1e7177da4c75a310faee3307cfa5991d7994c05d87e5be96b5929ba1650eab1a) // fixed_comms[44].y
                mstore(0x2b40, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[45].x
                mstore(0x2b60, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[45].y
                mstore(0x2b80, 0x0bcbedf43a04137bd5ef0f92512ae8bad807e96aaa5dbc2ed2a31641d4f11d66) // fixed_comms[46].x
                mstore(0x2ba0, 0x27885ac0a8e173e7e18d1be5c54d5d592262254d18ef80118c8aa6a9d11991f6) // fixed_comms[46].y
                mstore(0x2bc0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[47].x
                mstore(0x2be0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[47].y
                mstore(0x2c00, 0x1536b2e26a17d4c58b0b252c349095f46b6eb52dcaa9c0ec04d9f28e5e226978) // fixed_comms[48].x
                mstore(0x2c20, 0x09e0d6dd5ac7b0c6250af3ee502cc81138d487b27a721854fa0daa573602623d) // fixed_comms[48].y
                mstore(0x2c40, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[49].x
                mstore(0x2c60, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[49].y
                mstore(0x2c80, 0x0a178946de56e6b37c46f3371a273e20884a6c197043985bd64eb54601c0fc80) // fixed_comms[50].x
                mstore(0x2ca0, 0x26a2e52f5987bb8b7e3f8560547b2d467de9234d97d880b871919f1c36447ae0) // fixed_comms[50].y
                mstore(0x2cc0, 0x1eb01c3c81108ebdea23cd053baf06e2e605dc9ea4d3c6dfc13e9f426a236729) // fixed_comms[51].x
                mstore(0x2ce0, 0x2f8a9fbd39b2b549e4a2573cd2b049b1c02851f3b7fc7d14110c6898fd17a499) // fixed_comms[51].y
                mstore(0x2d00, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[52].x
                mstore(0x2d20, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[52].y
                mstore(0x2d40, 0x098db6b7774142cb76658315d6a62f61ef61f0c49afe372dcca8d2476e359f91) // fixed_comms[53].x
                mstore(0x2d60, 0x1a85789ec40cd498b6c4ce0b2aa681dcd0dff558dca153c80e42a3720973393c) // fixed_comms[53].y
                mstore(0x2d80, 0x156da1ede4eebaa801a8515f99fa75c8bd3ed641046fc353536bb838d8137117) // fixed_comms[54].x
                mstore(0x2da0, 0x16482ee0a17b5551edaec2113286a6f1124ae8c127765384b8ab3c7bddbd7320) // fixed_comms[54].y
                mstore(0x2dc0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[55].x
                mstore(0x2de0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[55].y
                mstore(0x2e00, 0x0c3f38215517310d9988e3b525fe9c81ce18217ea0a2b3b57c432bb6ce3c36d0) // fixed_comms[56].x
                mstore(0x2e20, 0x3031aeb7bef5625f701e906d8d787adabf001ea40cd108f3f18dddc83f8dbae7) // fixed_comms[56].y
                mstore(0x2e40, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[57].x
                mstore(0x2e60, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[57].y
                mstore(0x2e80, 0x07c56df6eb8634fafa4bbdf71a82d95065c80c8406f682929447332176320f73) // fixed_comms[58].x
                mstore(0x2ea0, 0x0dac77a25b47833eb038bf147552ca9f67c3860f900bcb31a330192dc4487d66) // fixed_comms[58].y
                mstore(0x2ec0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[59].x
                mstore(0x2ee0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[59].y
                mstore(0x2f00, 0x1554b8d632431c71f0f35cbfeb914473ccd23f2d6e8abaeb7853e5ba68e53074) // permutation_comms[0].x
                mstore(0x2f20, 0x143adf74cdf1d205546d80c237fffc265ef5e6b106d8c6700f3776d2908aa526) // permutation_comms[0].y
                mstore(0x2f40, 0x23e93e3ba7c359b9b71a74916c933da087f10d11420cbbde642902c81c4d1eb9) // permutation_comms[1].x
                mstore(0x2f60, 0x2ce5f32f9b8df7d02e63a17568836ea16f4a0573c3e8b0b1a6d9f63221bc5049) // permutation_comms[1].y
                mstore(0x2f80, 0x0e44685f69ebd93dad6b2e11b04fdd53eef3b417d1fdff6a18085b67192fc4d4) // permutation_comms[2].x
                mstore(0x2fa0, 0x2c432b784b1cc6a45a1e45e9742c024fda3f64f05ed9918820e1131e59784f06) // permutation_comms[2].y
                mstore(0x2fc0, 0x2fff04511af6d66894f3cfcbb3706e0ba4c8a1008f99c87aa24838ad933ce50c) // permutation_comms[3].x
                mstore(0x2fe0, 0x0f533906a1b598508b0429fad1f3de978cee2360b778492d1feae3ad8183df51) // permutation_comms[3].y
                mstore(0x3000, 0x08b08660eee7621f2f2080f4b82b782f0e13bdc670b8dd5f07ad4bcf7cfd9696) // permutation_comms[4].x
                mstore(0x3020, 0x26a40f86224603f31a94bd0696944a265acb29f1c3fcda7be6149b28fd527624) // permutation_comms[4].y
                mstore(0x3040, 0x2f4b11764cd12bac3ec865ec492b3c21c5f5a46fb9f1f899c00a81b3f649495c) // permutation_comms[5].x
                mstore(0x3060, 0x2095760612327648a3dd27e48d45a15eef56930d458186675e6fc72f14db4cba) // permutation_comms[5].y
                mstore(0x3080, 0x14d34b225dd8ecad5503db66d0cd4fe41ad6c318d6577921b10f2dcdd2f86748) // permutation_comms[6].x
                mstore(0x30a0, 0x2c5dd607a2771c21f5533f5ed1ed23f6443d0eec8d1ce8c2ebdeb209a823b8a6) // permutation_comms[6].y
                mstore(0x30c0, 0x24ccf40cc72d3d66d3dd8120a80325ffa9282b319d2577798a8d8c81dfe04ac9) // permutation_comms[7].x
                mstore(0x30e0, 0x2741cb192f1f5094e96bc3b6b4cf32e1ccd59cd246f27cc63533bbfd8e4ad293) // permutation_comms[7].y
                mstore(0x3100, 0x0158ce122978a22cc35417c75b47f3dc44c9a11aaf74eeeaceb2cdae84a35707) // permutation_comms[8].x
                mstore(0x3120, 0x12b01224c5fbfd842f5f5d22de0c1bf921cf3e7fab89439af42e7dc174835572) // permutation_comms[8].y
                mstore(0x3140, 0x0de4a6ebb5d2d438d1da232467da4a4a7facafca3bcaa76a1f230aeac80a7f1f) // permutation_comms[9].x
                mstore(0x3160, 0x1c2c5e9409cf1f7363d8d853f11f11c25433b0ac9b6cd3382dc4c2c294a7a3c1) // permutation_comms[9].y
                mstore(0x3180, 0x271459d5dad80d9350ce634003fcc0e8e9b2f8aaeaa510602e7d1f6b9dd74978) // permutation_comms[10].x
                mstore(0x31a0, 0x20015e9669509cd67f4caab89b99e816b1096bda0161e3924c2da974c1882513) // permutation_comms[10].y
                mstore(0x31c0, 0x011cc521a411a653a7035037814299d41fc0ebeb1111a4c686fc97f788224089) // permutation_comms[11].x
                mstore(0x31e0, 0x27d87b1072b5fcb927b12080f38f19dee58014c735aa9b2ffdc3692d2f4fdf17) // permutation_comms[11].y
                mstore(0x3200, 0x1f4d08aaaff83ef39cc169f70ccab6f968d76641e49b465443b616227ae6083b) // permutation_comms[12].x
                mstore(0x3220, 0x154fa55fc598b966b9e0ed1cd5afed705b6a178b84c391d9a131c71732602b3a) // permutation_comms[12].y
                mstore(0x3240, 0x2c89740f51432d5fb038f55c6db429b962796ef6b8c6ff679dde2621e7564240) // permutation_comms[13].x
                mstore(0x3260, 0x1653459eb9c7b346ec176616fc3fa0adf06e8bde0f202e0d71c2ea3222eeae55) // permutation_comms[13].y
                mstore(0x3280, 0x05ddf7b64265a4b4da2f1aad41dc5487c359dae41b8bd49fcb52a3b55f2bf7d7) // permutation_comms[14].x
                mstore(0x32a0, 0x26b12d8d2529d66936f59dd075b6fa6b616ae266ea7f9ac9e75b3d773fea0ef6) // permutation_comms[14].y
                mstore(0x32c0, 0x095e9d55ad591fc6381d4589f98777b4fea1b757ec00253b34a0f6c6866cf2ce) // permutation_comms[15].x
                mstore(0x32e0, 0x06c4f6c3826fd59713969a272a6f0c4fef8566e7837bd139fc579c1ffbff20c8) // permutation_comms[15].y
                mstore(0x3300, 0x2bfea8d6cae27367df7464142021525651cc0251990999e33414a4faed8cb1fb) // permutation_comms[16].x
                mstore(0x3320, 0x17ad0197936b0e3cfc4d146fb9cbc1b67ba25472242c1b8b8ccaa32b475c65ed) // permutation_comms[16].y
                mstore(0x3340, 0x220d738e3652dbeea234aba6fc4528e7101f5eff43b72d49eb11afde2d73617b) // permutation_comms[17].x
                mstore(0x3360, 0x1bbc0318fd737282b258ea45d70abef39bcaafa1c8a828fe3e8bf46a3c375f99) // permutation_comms[17].y
                mstore(0x3380, 0x2ca34383c4ef8f7544e45488ee1f16a0c9a6dc1e5f418488108d1fe889d3817d) // permutation_comms[18].x
                mstore(0x33a0, 0x0c3f2d61a40ffe4c5e377ff9527d5746a6a41daf22bbc32e89334da78d3a1cbd) // permutation_comms[18].y
                mstore(0x33c0, 0x0fa18265d0ae6381bd5e473009d7bccadbb157f65393b699d429cb80d1d7172e) // permutation_comms[19].x
                mstore(0x33e0, 0x2ec09f0716387f3629fbd51a46d90e28d1887dc959e486158424fc07b8600f1b) // permutation_comms[19].y
                mstore(0x3400, 0x0d89e617e95ed0acf8b1fa015b9e98c1b0b7f6a292719debd595845d2a7bcb37) // permutation_comms[20].x
                mstore(0x3420, 0x1b5f66749391e566122158da67daae74a55d90c50c7d4ba662ccb976e4096cc6) // permutation_comms[20].y
                mstore(0x3440, 0x296d5bd57bb648d1507f4d22572ab8a67928e8e2a56ed2f53699222007e0106e) // permutation_comms[21].x
                mstore(0x3460, 0x1ec8d704e79350284573f37921370c09c791f076717feca1db02f729800adf19) // permutation_comms[21].y
                mstore(0x3480, 0x116eb275635cd59e37aa14453c7873c2a2796694393a64a095a370f1c7d2059d) // permutation_comms[22].x
                mstore(0x34a0, 0x2a17147941b0dc2bca8ff9c8c1e688a4377975890a3f1694e305256e4ff6f62d) // permutation_comms[22].y
                mstore(0x34c0, 0x1e50b562aee3963d3bef9d2dac52aebcfa30c59af77eb21926930b7e7fd62ec2) // permutation_comms[23].x
                mstore(0x34e0, 0x1fb8d8311b5253399582ff8a571f09fe60a236441d8195336cddb6289fd465f5) // permutation_comms[23].y
                mstore(0x3500, 0x1a2ef992057c112e8f2b8cc09ec8a1d557ebc53fccfb082bd39aa59d70cb7445) // permutation_comms[24].x
                mstore(0x3520, 0x0911f65905e966e972e677330296f0b0a4c9ca83c2f79ded5ab5cd1e11c2c620) // permutation_comms[24].y
                mstore(0x3540, 0x039bfa98ff4d2d4d38d0d3906f852a38128358eb61be8793a33892168565d20d) // permutation_comms[25].x
                mstore(0x3560, 0x0b524b15e2a8bfa8c77fcb6a66efcf7bc120a49e4062bf594a33af421b810fa1) // permutation_comms[25].y
                mstore(0x3580, 0x019c5461753817ba162a76e440d22506b2ed8ed4dd4b450d500671b37a90ef3c) // permutation_comms[26].x
                mstore(0x35a0, 0x0a80a2980b7607da540e46009875708be9a467cdfca3bff07d38400064ff07eb) // permutation_comms[26].y
                mstore(0x35c0, 0x2914a965555483d77558452d1835fb2d9cbe7e2578119ac42358dc562bc9bfe2) // permutation_comms[27].x
                mstore(0x35e0, 0x210c4bf0daae2eab2725e85848aa1adef21527e13d35a14036d551e1b38b3061) // permutation_comms[27].y
                mstore(0x3600, 0x1b0ff7d2308e21e8b67384ce8ee7d986d703fa9fab4ad965acf13f03da35fe87) // permutation_comms[28].x
                mstore(0x3620, 0x0b12f05530e427fd5de235f96a759b7466919080cca11c4f90d362c9f6e3a9eb) // permutation_comms[28].y
                mstore(0x3640, 0x087c607a4044b88913bd5bba06a67808a0c4e15ed8f2cf2bc2c04d2599850200) // permutation_comms[29].x
                mstore(0x3660, 0x25dfa188dce6400bfa05a508aac7577892c9b7abf6c2f512153b1e07ba1f6405) // permutation_comms[29].y
                mstore(0x3680, 0x1ba486d24b4489ce7e4f36614b7c46b95b84dbf4fc3d48294d506281af899d5f) // permutation_comms[30].x
                mstore(0x36a0, 0x1c5de30fd87d3d687c524fd4e20b8143d88612c699533adf398f02f52f71dd52) // permutation_comms[30].y
                mstore(0x36c0, 0x1a36d0aab61937c2ab75687af01f9dfff8645b37c75f127117269e4242b4d667) // permutation_comms[31].x
                mstore(0x36e0, 0x108804a96cd9e48606757de5d1df02af6e333db1aff3158c50446777c4a179a2) // permutation_comms[31].y
                mstore(0x3700, 0x2b29eedb685e78332b0fff19aecfae8c19e630de64a2e7c1ff32c1ae5573fa07) // permutation_comms[32].x
                mstore(0x3720, 0x06924e350d2e2df6aeea899b32a7784cbe951a1c13f6d5f5b8389191b6ec7807) // permutation_comms[32].y
                mstore(0x3740, 0x0542e3554293dbe096d5bf841a5a93a22f7a6ba32e0b20d67bd1956b8aff22f4) // permutation_comms[33].x
                mstore(0x3760, 0x0490cd75e455f587f192583ef292bb78a95d0d8d585755a439c840e6c9c433f4) // permutation_comms[33].y
                mstore(0x3780, 0x30093b942774d73c33a0cbcee540eeefa2a8dd45d8aa10b68e75c0200dc7ee9d) // permutation_comms[34].x
                mstore(0x37a0, 0x1e0ce1bde89b7e6b5591b7d09abd0e4090ef5c7f97eb2fc01c66ad05cc710042) // permutation_comms[34].y
                mstore(0x37c0, 0x20eabf16207c1fe479d896cfa92126f31598d87668d0531a0ae9cdf4c499e96f) // permutation_comms[35].x
                mstore(0x37e0, 0x2e29c702d327a2ff29080eff1ca74626a98a67deb5a240fe8460f5edf885e2b9) // permutation_comms[35].y
                mstore(0x3800, 0x05e474c013c2870a2656b1ed9df6a49a9cdd6b61ca7de03145dfade1e6be7d62) // permutation_comms[36].x
                mstore(0x3820, 0x19a309a23661434cd6b896ee26fb489b2cc37383b9675097492156113c097468) // permutation_comms[36].y
                mstore(0x3840, 0x0a769335308fadfce2a0884585711b9aad0a4b4ba71430dc2a22f9f5b7b3b6fc) // permutation_comms[37].x
                mstore(0x3860, 0x09c1da773c8283e2e39353109623771f32ce1708c3aaa8d6f1c8efae050dfb88) // permutation_comms[37].y
                mstore(0x3880, 0x0a5c318c4e1e307cf74d477e301a5252565d9331357203dd9a8bf1719e0f20ce) // permutation_comms[38].x
                mstore(0x38a0, 0x01bd34e00d4b4c241b3a6c13f74630ec91c1f9056d61adf2cc5fdc4c927153af) // permutation_comms[38].y
                mstore(0x38c0, 0x12a655f98a487de23bba117aedcc8c644c1d82d683b580b13dca7a6efdf253b5) // permutation_comms[39].x
                mstore(0x38e0, 0x205c1e852035e893bfe6640533cf80bda8fc265d2f05ff91bf5d2ef550d90d01) // permutation_comms[39].y
                mstore(0x3900, 0x2f72ab455fef4bc4c753d1fbc9787d233ba1064a2d6d9f0108f21d4acc11bbfa) // permutation_comms[40].x
                mstore(0x3920, 0x2a7913c2497017394a270b2c69cccf4999355b8ce1044e72797c91da60642740) // permutation_comms[40].y

                // Check valid length of proof
                success := and(success, eq(0x32c0, calldataload(PROOF_LEN_CPTR)))

                // Check valid length of instances
                let num_instances := mload(NUM_INSTANCES_MPTR)
                success := and(success, eq(num_instances, calldataload(NUM_INSTANCE_CPTR)))

                // Absorb vk diegst
                mstore(0x00, mload(VK_DIGEST_MPTR))

                // Read instances and witness commitments and generate challenges
                let hash_mptr := 0x20
                let instance_cptr := INSTANCE_CPTR
                for
                    { let instance_cptr_end := add(instance_cptr, mul(0x20, num_instances)) }
                    lt(instance_cptr, instance_cptr_end)
                    {}
                {
                    let instance := calldataload(instance_cptr)
                    success := and(success, lt(instance, r))
                    mstore(hash_mptr, instance)
                    instance_cptr := add(instance_cptr, 0x20)
                    hash_mptr := add(hash_mptr, 0x20)
                }

                let proof_cptr := PROOF_CPTR
                let challenge_mptr := CHALLENGE_MPTR

                // Phase 1
                for
                    { let proof_cptr_end := add(proof_cptr, 0x09c0) }
                    lt(proof_cptr, proof_cptr_end)
                    {}
                {
                    success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q)
                }

                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)

                // Phase 2
                for
                    { let proof_cptr_end := add(proof_cptr, 0x0340) }
                    lt(proof_cptr, proof_cptr_end)
                    {}
                {
                    success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q)
                }

                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)
                challenge_mptr := squeeze_challenge_cont(challenge_mptr, r)

                // Phase 3
                for
                    { let proof_cptr_end := add(proof_cptr, 0x0700) }
                    lt(proof_cptr, proof_cptr_end)
                    {}
                {
                    success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q)
                }

                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)

                // Phase 4
                for
                    { let proof_cptr_end := add(proof_cptr, 0x0100) }
                    lt(proof_cptr, proof_cptr_end)
                    {}
                {
                    success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q)
                }

                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)

                // Read evaluations
                for
                    { let proof_cptr_end := add(proof_cptr, 0x1d40) }
                    lt(proof_cptr, proof_cptr_end)
                    {}
                {
                    let eval := calldataload(proof_cptr)
                    success := and(success, lt(eval, r))
                    mstore(hash_mptr, eval)
                    proof_cptr := add(proof_cptr, 0x20)
                    hash_mptr := add(hash_mptr, 0x20)
                }

                // Read batch opening proof and generate challenges
                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)       // zeta
                challenge_mptr := squeeze_challenge_cont(challenge_mptr, r)                        // nu

                success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q) // W

                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)       // mu

                success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q) // W'

                // Read accumulator from instances
                if mload(HAS_ACCUMULATOR_MPTR) {
                    let num_limbs := mload(NUM_ACC_LIMBS_MPTR)
                    let num_limb_bits := mload(NUM_ACC_LIMB_BITS_MPTR)

                    let cptr := add(INSTANCE_CPTR, mul(mload(ACC_OFFSET_MPTR), 0x20))
                    let lhs_y_off := mul(num_limbs, 0x20)
                    let rhs_x_off := mul(lhs_y_off, 2)
                    let rhs_y_off := mul(lhs_y_off, 3)
                    let lhs_x := calldataload(cptr)
                    let lhs_y := calldataload(add(cptr, lhs_y_off))
                    let rhs_x := calldataload(add(cptr, rhs_x_off))
                    let rhs_y := calldataload(add(cptr, rhs_y_off))
                    for
                        {
                            let cptr_end := add(cptr, mul(0x20, num_limbs))
                            let shift := num_limb_bits
                        }
                        lt(cptr, cptr_end)
                        {}
                    {
                        cptr := add(cptr, 0x20)
                        lhs_x := add(lhs_x, shl(shift, calldataload(cptr)))
                        lhs_y := add(lhs_y, shl(shift, calldataload(add(cptr, lhs_y_off))))
                        rhs_x := add(rhs_x, shl(shift, calldataload(add(cptr, rhs_x_off))))
                        rhs_y := add(rhs_y, shl(shift, calldataload(add(cptr, rhs_y_off))))
                        shift := add(shift, num_limb_bits)
                    }

                    success := and(success, eq(mulmod(lhs_y, lhs_y, q), addmod(mulmod(lhs_x, mulmod(lhs_x, lhs_x, q), q), 3, q)))
                    success := and(success, eq(mulmod(rhs_y, rhs_y, q), addmod(mulmod(rhs_x, mulmod(rhs_x, rhs_x, q), q), 3, q)))

                    mstore(ACC_LHS_X_MPTR, lhs_x)
                    mstore(ACC_LHS_Y_MPTR, lhs_y)
                    mstore(ACC_RHS_X_MPTR, rhs_x)
                    mstore(ACC_RHS_Y_MPTR, rhs_y)
                }

                pop(q)
            }

            // Revert earlier if anything from calldata is invalid
            if iszero(success) {
                revert(0, 0)
            }

            // Compute lagrange evaluations and instance evaluation
            {
                let k := mload(K_MPTR)
                let x := mload(X_MPTR)
                let x_n := x
                for
                    { let idx := 0 }
                    lt(idx, k)
                    { idx := add(idx, 1) }
                {
                    x_n := mulmod(x_n, x_n, r)
                }

                let omega := mload(OMEGA_MPTR)

                let mptr := X_N_MPTR
                let mptr_end := add(mptr, mul(0x20, add(mload(NUM_INSTANCES_MPTR), 6)))
                for
                    { let pow_of_omega := mload(OMEGA_INV_TO_L_MPTR) }
                    lt(mptr, mptr_end)
                    { mptr := add(mptr, 0x20) }
                {
                    mstore(mptr, addmod(x, sub(r, pow_of_omega), r))
                    pow_of_omega := mulmod(pow_of_omega, omega, r)
                }
                let x_n_minus_1 := addmod(x_n, sub(r, 1), r)
                mstore(mptr_end, x_n_minus_1)
                success := batch_invert(success, X_N_MPTR, add(mptr_end, 0x20), r)

                mptr := X_N_MPTR
                let l_i_common := mulmod(x_n_minus_1, mload(N_INV_MPTR), r)
                for
                    { let pow_of_omega := mload(OMEGA_INV_TO_L_MPTR) }
                    lt(mptr, mptr_end)
                    { mptr := add(mptr, 0x20) }
                {
                    mstore(mptr, mulmod(l_i_common, mulmod(mload(mptr), pow_of_omega, r), r))
                    pow_of_omega := mulmod(pow_of_omega, omega, r)
                }

                let l_blind := mload(add(X_N_MPTR, 0x20))
                let l_i_cptr := add(X_N_MPTR, 0x40)
                for
                    { let l_i_cptr_end := add(X_N_MPTR, 0xc0) }
                    lt(l_i_cptr, l_i_cptr_end)
                    { l_i_cptr := add(l_i_cptr, 0x20) }
                {
                    l_blind := addmod(l_blind, mload(l_i_cptr), r)
                }

                let instance_eval := mulmod(mload(l_i_cptr), calldataload(INSTANCE_CPTR), r)
                let instance_cptr := add(INSTANCE_CPTR, 0x20)
                l_i_cptr := add(l_i_cptr, 0x20)
                for
                    { let instance_cptr_end := add(INSTANCE_CPTR, mul(0x20, mload(NUM_INSTANCES_MPTR))) }
                    lt(instance_cptr, instance_cptr_end)
                    {
                        instance_cptr := add(instance_cptr, 0x20)
                        l_i_cptr := add(l_i_cptr, 0x20)
                    }
                {
                    instance_eval := addmod(instance_eval, mulmod(mload(l_i_cptr), calldataload(instance_cptr), r), r)
                }

                let x_n_minus_1_inv := mload(mptr_end)
                let l_last := mload(X_N_MPTR)
                let l_0 := mload(add(X_N_MPTR, 0xc0))

                mstore(X_N_MPTR, x_n)
                mstore(X_N_MINUS_1_INV_MPTR, x_n_minus_1_inv)
                mstore(L_LAST_MPTR, l_last)
                mstore(L_BLIND_MPTR, l_blind)
                mstore(L_0_MPTR, l_0)
                mstore(INSTANCE_EVAL_MPTR, instance_eval)
            }

            // Compute quotient evavluation
            {
                let quotient_eval_numer
                let delta := 4131629893567559867359510883348571134090853742863529169391034518566172092834
                let y := mload(Y_MPTR)
                {
                    let f_16 := calldataload(0x1de4)
                    let var0 := 0x1
                    let var1 := sub(r, f_16)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_16, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_26 := calldataload(0x18a4)
                    let a_0 := calldataload(0x1564)
                    let a_13 := calldataload(0x1704)
                    let var7 := mulmod(a_0, a_13, r)
                    let a_26_prev_1 := calldataload(0x1a44)
                    let var8 := addmod(var7, a_26_prev_1, r)
                    let var9 := sub(r, var8)
                    let var10 := addmod(a_26, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := var11
                }
                {
                    let f_20 := calldataload(0x1e64)
                    let var0 := 0x2
                    let var1 := sub(r, f_20)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_20, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_27 := calldataload(0x18c4)
                    let a_1 := calldataload(0x1584)
                    let a_14 := calldataload(0x1724)
                    let var7 := mulmod(a_1, a_14, r)
                    let a_27_prev_1 := calldataload(0x1a64)
                    let var8 := addmod(var7, a_27_prev_1, r)
                    let var9 := sub(r, var8)
                    let var10 := addmod(a_27, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_23 := calldataload(0x1ec4)
                    let var0 := 0x1
                    let var1 := sub(r, f_23)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_23, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_28 := calldataload(0x18e4)
                    let a_2 := calldataload(0x15a4)
                    let a_15 := calldataload(0x1744)
                    let var7 := mulmod(a_2, a_15, r)
                    let a_28_prev_1 := calldataload(0x1a84)
                    let var8 := addmod(var7, a_28_prev_1, r)
                    let var9 := sub(r, var8)
                    let var10 := addmod(a_28, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_26 := calldataload(0x1f24)
                    let var0 := 0x1
                    let var1 := sub(r, f_26)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_26, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_29 := calldataload(0x1904)
                    let a_3 := calldataload(0x15c4)
                    let a_16 := calldataload(0x1764)
                    let var7 := mulmod(a_3, a_16, r)
                    let a_29_prev_1 := calldataload(0x1aa4)
                    let var8 := addmod(var7, a_29_prev_1, r)
                    let var9 := sub(r, var8)
                    let var10 := addmod(a_29, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_30 := calldataload(0x1fa4)
                    let var0 := 0x2
                    let var1 := sub(r, f_30)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_30, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_30 := calldataload(0x1924)
                    let a_4 := calldataload(0x15e4)
                    let a_17 := calldataload(0x1784)
                    let var7 := mulmod(a_4, a_17, r)
                    let a_30_prev_1 := calldataload(0x1ac4)
                    let var8 := addmod(var7, a_30_prev_1, r)
                    let var9 := sub(r, var8)
                    let var10 := addmod(a_30, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_33 := calldataload(0x2004)
                    let var0 := 0x1
                    let var1 := sub(r, f_33)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_33, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_31 := calldataload(0x1944)
                    let a_5 := calldataload(0x1604)
                    let a_18 := calldataload(0x17a4)
                    let var7 := mulmod(a_5, a_18, r)
                    let a_31_prev_1 := calldataload(0x1ae4)
                    let var8 := addmod(var7, a_31_prev_1, r)
                    let var9 := sub(r, var8)
                    let var10 := addmod(a_31, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_36 := calldataload(0x2064)
                    let var0 := 0x1
                    let var1 := sub(r, f_36)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_36, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_32 := calldataload(0x1964)
                    let a_6 := calldataload(0x1624)
                    let a_19 := calldataload(0x17c4)
                    let var7 := mulmod(a_6, a_19, r)
                    let a_32_prev_1 := calldataload(0x1b04)
                    let var8 := addmod(var7, a_32_prev_1, r)
                    let var9 := sub(r, var8)
                    let var10 := addmod(a_32, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_40 := calldataload(0x20e4)
                    let var0 := 0x2
                    let var1 := sub(r, f_40)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_40, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_33 := calldataload(0x1984)
                    let a_7 := calldataload(0x1644)
                    let a_20 := calldataload(0x17e4)
                    let var7 := mulmod(a_7, a_20, r)
                    let a_33_prev_1 := calldataload(0x1b24)
                    let var8 := addmod(var7, a_33_prev_1, r)
                    let var9 := sub(r, var8)
                    let var10 := addmod(a_33, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_43 := calldataload(0x2144)
                    let var0 := 0x1
                    let var1 := sub(r, f_43)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_43, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_34 := calldataload(0x19a4)
                    let a_8 := calldataload(0x1664)
                    let a_21 := calldataload(0x1804)
                    let var7 := mulmod(a_8, a_21, r)
                    let a_34_prev_1 := calldataload(0x1b44)
                    let var8 := addmod(var7, a_34_prev_1, r)
                    let var9 := sub(r, var8)
                    let var10 := addmod(a_34, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_46 := calldataload(0x21a4)
                    let var0 := 0x1
                    let var1 := sub(r, f_46)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_46, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_35 := calldataload(0x19c4)
                    let a_9 := calldataload(0x1684)
                    let a_22 := calldataload(0x1824)
                    let var7 := mulmod(a_9, a_22, r)
                    let a_35_prev_1 := calldataload(0x1b64)
                    let var8 := addmod(var7, a_35_prev_1, r)
                    let var9 := sub(r, var8)
                    let var10 := addmod(a_35, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_50 := calldataload(0x2224)
                    let var0 := 0x2
                    let var1 := sub(r, f_50)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_50, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_36 := calldataload(0x19e4)
                    let a_10 := calldataload(0x16a4)
                    let a_23 := calldataload(0x1844)
                    let var7 := mulmod(a_10, a_23, r)
                    let a_36_prev_1 := calldataload(0x1b84)
                    let var8 := addmod(var7, a_36_prev_1, r)
                    let var9 := sub(r, var8)
                    let var10 := addmod(a_36, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_53 := calldataload(0x2284)
                    let var0 := 0x1
                    let var1 := sub(r, f_53)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_53, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_37 := calldataload(0x1a04)
                    let a_11 := calldataload(0x16c4)
                    let a_24 := calldataload(0x1864)
                    let var7 := mulmod(a_11, a_24, r)
                    let a_37_prev_1 := calldataload(0x1ba4)
                    let var8 := addmod(var7, a_37_prev_1, r)
                    let var9 := sub(r, var8)
                    let var10 := addmod(a_37, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_56 := calldataload(0x22e4)
                    let var0 := 0x1
                    let var1 := sub(r, f_56)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_56, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_38 := calldataload(0x1a24)
                    let a_12 := calldataload(0x16e4)
                    let a_25 := calldataload(0x1884)
                    let var7 := mulmod(a_12, a_25, r)
                    let a_38_prev_1 := calldataload(0x1bc4)
                    let var8 := addmod(var7, a_38_prev_1, r)
                    let var9 := sub(r, var8)
                    let var10 := addmod(a_38, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_17 := calldataload(0x1e04)
                    let var0 := 0x2
                    let var1 := sub(r, f_17)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_17, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_26 := calldataload(0x18a4)
                    let a_13 := calldataload(0x1704)
                    let a_26_prev_1 := calldataload(0x1a44)
                    let var7 := mulmod(a_13, a_26_prev_1, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_26, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_20 := calldataload(0x1e64)
                    let var0 := 0x1
                    let var1 := sub(r, f_20)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_20, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_27 := calldataload(0x18c4)
                    let a_14 := calldataload(0x1724)
                    let a_27_prev_1 := calldataload(0x1a64)
                    let var7 := mulmod(a_14, a_27_prev_1, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_27, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_23 := calldataload(0x1ec4)
                    let var0 := 0x1
                    let var1 := sub(r, f_23)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_23, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_28 := calldataload(0x18e4)
                    let a_15 := calldataload(0x1744)
                    let a_28_prev_1 := calldataload(0x1a84)
                    let var7 := mulmod(a_15, a_28_prev_1, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_28, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_27 := calldataload(0x1f44)
                    let var0 := 0x2
                    let var1 := sub(r, f_27)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_27, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_29 := calldataload(0x1904)
                    let a_16 := calldataload(0x1764)
                    let a_29_prev_1 := calldataload(0x1aa4)
                    let var7 := mulmod(a_16, a_29_prev_1, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_29, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_30 := calldataload(0x1fa4)
                    let var0 := 0x1
                    let var1 := sub(r, f_30)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_30, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_30 := calldataload(0x1924)
                    let a_17 := calldataload(0x1784)
                    let a_30_prev_1 := calldataload(0x1ac4)
                    let var7 := mulmod(a_17, a_30_prev_1, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_30, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_33 := calldataload(0x2004)
                    let var0 := 0x1
                    let var1 := sub(r, f_33)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_33, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_31 := calldataload(0x1944)
                    let a_18 := calldataload(0x17a4)
                    let a_31_prev_1 := calldataload(0x1ae4)
                    let var7 := mulmod(a_18, a_31_prev_1, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_31, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_37 := calldataload(0x2084)
                    let var0 := 0x2
                    let var1 := sub(r, f_37)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_37, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_32 := calldataload(0x1964)
                    let a_19 := calldataload(0x17c4)
                    let a_32_prev_1 := calldataload(0x1b04)
                    let var7 := mulmod(a_19, a_32_prev_1, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_32, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_40 := calldataload(0x20e4)
                    let var0 := 0x1
                    let var1 := sub(r, f_40)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_40, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_33 := calldataload(0x1984)
                    let a_20 := calldataload(0x17e4)
                    let a_33_prev_1 := calldataload(0x1b24)
                    let var7 := mulmod(a_20, a_33_prev_1, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_33, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_43 := calldataload(0x2144)
                    let var0 := 0x1
                    let var1 := sub(r, f_43)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_43, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_34 := calldataload(0x19a4)
                    let a_21 := calldataload(0x1804)
                    let a_34_prev_1 := calldataload(0x1b44)
                    let var7 := mulmod(a_21, a_34_prev_1, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_34, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_47 := calldataload(0x21c4)
                    let var0 := 0x2
                    let var1 := sub(r, f_47)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_47, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_35 := calldataload(0x19c4)
                    let a_22 := calldataload(0x1824)
                    let a_35_prev_1 := calldataload(0x1b64)
                    let var7 := mulmod(a_22, a_35_prev_1, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_35, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_50 := calldataload(0x2224)
                    let var0 := 0x1
                    let var1 := sub(r, f_50)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_50, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_36 := calldataload(0x19e4)
                    let a_23 := calldataload(0x1844)
                    let a_36_prev_1 := calldataload(0x1b84)
                    let var7 := mulmod(a_23, a_36_prev_1, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_36, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_53 := calldataload(0x2284)
                    let var0 := 0x1
                    let var1 := sub(r, f_53)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_53, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_37 := calldataload(0x1a04)
                    let a_24 := calldataload(0x1864)
                    let a_37_prev_1 := calldataload(0x1ba4)
                    let var7 := mulmod(a_24, a_37_prev_1, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_37, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_57 := calldataload(0x2304)
                    let var0 := 0x2
                    let var1 := sub(r, f_57)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_57, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_38 := calldataload(0x1a24)
                    let a_25 := calldataload(0x1884)
                    let a_38_prev_1 := calldataload(0x1bc4)
                    let var7 := mulmod(a_25, a_38_prev_1, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_38, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_18 := calldataload(0x1e24)
                    let var0 := 0x1
                    let var1 := sub(r, f_18)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_18, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_26 := calldataload(0x18a4)
                    let a_13 := calldataload(0x1704)
                    let var7 := sub(r, a_13)
                    let var8 := addmod(a_26, var7, r)
                    let var9 := mulmod(var6, var8, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var9, r)
                }
                {
                    let f_22 := calldataload(0x1ea4)
                    let var0 := 0x2
                    let var1 := sub(r, f_22)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_22, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_27 := calldataload(0x18c4)
                    let a_14 := calldataload(0x1724)
                    let var7 := sub(r, a_14)
                    let var8 := addmod(a_27, var7, r)
                    let var9 := mulmod(var6, var8, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var9, r)
                }
                {
                    let f_25 := calldataload(0x1f04)
                    let var0 := 0x1
                    let var1 := sub(r, f_25)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_25, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_28 := calldataload(0x18e4)
                    let a_15 := calldataload(0x1744)
                    let var7 := sub(r, a_15)
                    let var8 := addmod(a_28, var7, r)
                    let var9 := mulmod(var6, var8, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var9, r)
                }
                {
                    let f_28 := calldataload(0x1f64)
                    let var0 := 0x1
                    let var1 := sub(r, f_28)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_28, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_29 := calldataload(0x1904)
                    let a_16 := calldataload(0x1764)
                    let var7 := sub(r, a_16)
                    let var8 := addmod(a_29, var7, r)
                    let var9 := mulmod(var6, var8, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var9, r)
                }
                {
                    let f_32 := calldataload(0x1fe4)
                    let var0 := 0x2
                    let var1 := sub(r, f_32)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_32, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_30 := calldataload(0x1924)
                    let a_17 := calldataload(0x1784)
                    let var7 := sub(r, a_17)
                    let var8 := addmod(a_30, var7, r)
                    let var9 := mulmod(var6, var8, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var9, r)
                }
                {
                    let f_35 := calldataload(0x2044)
                    let var0 := 0x1
                    let var1 := sub(r, f_35)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_35, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_31 := calldataload(0x1944)
                    let a_18 := calldataload(0x17a4)
                    let var7 := sub(r, a_18)
                    let var8 := addmod(a_31, var7, r)
                    let var9 := mulmod(var6, var8, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var9, r)
                }
                {
                    let f_38 := calldataload(0x20a4)
                    let var0 := 0x1
                    let var1 := sub(r, f_38)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_38, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_32 := calldataload(0x1964)
                    let a_19 := calldataload(0x17c4)
                    let var7 := sub(r, a_19)
                    let var8 := addmod(a_32, var7, r)
                    let var9 := mulmod(var6, var8, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var9, r)
                }
                {
                    let f_42 := calldataload(0x2124)
                    let var0 := 0x2
                    let var1 := sub(r, f_42)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_42, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_33 := calldataload(0x1984)
                    let a_20 := calldataload(0x17e4)
                    let var7 := sub(r, a_20)
                    let var8 := addmod(a_33, var7, r)
                    let var9 := mulmod(var6, var8, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var9, r)
                }
                {
                    let f_45 := calldataload(0x2184)
                    let var0 := 0x1
                    let var1 := sub(r, f_45)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_45, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_34 := calldataload(0x19a4)
                    let a_21 := calldataload(0x1804)
                    let var7 := sub(r, a_21)
                    let var8 := addmod(a_34, var7, r)
                    let var9 := mulmod(var6, var8, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var9, r)
                }
                {
                    let f_48 := calldataload(0x21e4)
                    let var0 := 0x1
                    let var1 := sub(r, f_48)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_48, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_35 := calldataload(0x19c4)
                    let a_22 := calldataload(0x1824)
                    let var7 := sub(r, a_22)
                    let var8 := addmod(a_35, var7, r)
                    let var9 := mulmod(var6, var8, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var9, r)
                }
                {
                    let f_52 := calldataload(0x2264)
                    let var0 := 0x2
                    let var1 := sub(r, f_52)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_52, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_36 := calldataload(0x19e4)
                    let a_23 := calldataload(0x1844)
                    let var7 := sub(r, a_23)
                    let var8 := addmod(a_36, var7, r)
                    let var9 := mulmod(var6, var8, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var9, r)
                }
                {
                    let f_55 := calldataload(0x22c4)
                    let var0 := 0x1
                    let var1 := sub(r, f_55)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_55, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_37 := calldataload(0x1a04)
                    let a_24 := calldataload(0x1864)
                    let var7 := sub(r, a_24)
                    let var8 := addmod(a_37, var7, r)
                    let var9 := mulmod(var6, var8, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var9, r)
                }
                {
                    let f_58 := calldataload(0x2324)
                    let var0 := 0x1
                    let var1 := sub(r, f_58)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_58, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_38 := calldataload(0x1a24)
                    let a_25 := calldataload(0x1884)
                    let var7 := sub(r, a_25)
                    let var8 := addmod(a_38, var7, r)
                    let var9 := mulmod(var6, var8, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var9, r)
                }
                {
                    let f_16 := calldataload(0x1de4)
                    let var0 := 0x2
                    let var1 := sub(r, f_16)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_16, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_26 := calldataload(0x18a4)
                    let a_0 := calldataload(0x1564)
                    let a_13 := calldataload(0x1704)
                    let var7 := addmod(a_0, a_13, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_26, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_19 := calldataload(0x1e44)
                    let var0 := 0x1
                    let var1 := sub(r, f_19)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_19, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_27 := calldataload(0x18c4)
                    let a_1 := calldataload(0x1584)
                    let a_14 := calldataload(0x1724)
                    let var7 := addmod(a_1, a_14, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_27, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_22 := calldataload(0x1ea4)
                    let var0 := 0x1
                    let var1 := sub(r, f_22)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_22, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_28 := calldataload(0x18e4)
                    let a_2 := calldataload(0x15a4)
                    let a_15 := calldataload(0x1744)
                    let var7 := addmod(a_2, a_15, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_28, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_26 := calldataload(0x1f24)
                    let var0 := 0x2
                    let var1 := sub(r, f_26)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_26, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_29 := calldataload(0x1904)
                    let a_3 := calldataload(0x15c4)
                    let a_16 := calldataload(0x1764)
                    let var7 := addmod(a_3, a_16, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_29, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_29 := calldataload(0x1f84)
                    let var0 := 0x1
                    let var1 := sub(r, f_29)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_29, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_30 := calldataload(0x1924)
                    let a_4 := calldataload(0x15e4)
                    let a_17 := calldataload(0x1784)
                    let var7 := addmod(a_4, a_17, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_30, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_32 := calldataload(0x1fe4)
                    let var0 := 0x1
                    let var1 := sub(r, f_32)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_32, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_31 := calldataload(0x1944)
                    let a_5 := calldataload(0x1604)
                    let a_18 := calldataload(0x17a4)
                    let var7 := addmod(a_5, a_18, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_31, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_36 := calldataload(0x2064)
                    let var0 := 0x2
                    let var1 := sub(r, f_36)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_36, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_32 := calldataload(0x1964)
                    let a_6 := calldataload(0x1624)
                    let a_19 := calldataload(0x17c4)
                    let var7 := addmod(a_6, a_19, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_32, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_39 := calldataload(0x20c4)
                    let var0 := 0x1
                    let var1 := sub(r, f_39)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_39, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_33 := calldataload(0x1984)
                    let a_7 := calldataload(0x1644)
                    let a_20 := calldataload(0x17e4)
                    let var7 := addmod(a_7, a_20, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_33, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_42 := calldataload(0x2124)
                    let var0 := 0x1
                    let var1 := sub(r, f_42)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_42, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_34 := calldataload(0x19a4)
                    let a_8 := calldataload(0x1664)
                    let a_21 := calldataload(0x1804)
                    let var7 := addmod(a_8, a_21, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_34, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_46 := calldataload(0x21a4)
                    let var0 := 0x2
                    let var1 := sub(r, f_46)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_46, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_35 := calldataload(0x19c4)
                    let a_9 := calldataload(0x1684)
                    let a_22 := calldataload(0x1824)
                    let var7 := addmod(a_9, a_22, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_35, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_49 := calldataload(0x2204)
                    let var0 := 0x1
                    let var1 := sub(r, f_49)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_49, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_36 := calldataload(0x19e4)
                    let a_10 := calldataload(0x16a4)
                    let a_23 := calldataload(0x1844)
                    let var7 := addmod(a_10, a_23, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_36, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_52 := calldataload(0x2264)
                    let var0 := 0x1
                    let var1 := sub(r, f_52)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_52, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_37 := calldataload(0x1a04)
                    let a_11 := calldataload(0x16c4)
                    let a_24 := calldataload(0x1864)
                    let var7 := addmod(a_11, a_24, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_37, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_56 := calldataload(0x22e4)
                    let var0 := 0x2
                    let var1 := sub(r, f_56)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_56, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_38 := calldataload(0x1a24)
                    let a_12 := calldataload(0x16e4)
                    let a_25 := calldataload(0x1884)
                    let var7 := addmod(a_12, a_25, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_38, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_18 := calldataload(0x1e24)
                    let var0 := 0x2
                    let var1 := sub(r, f_18)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_18, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_26 := calldataload(0x18a4)
                    let a_0 := calldataload(0x1564)
                    let a_13 := calldataload(0x1704)
                    let var7 := mulmod(a_0, a_13, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_26, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_21 := calldataload(0x1e84)
                    let var0 := 0x1
                    let var1 := sub(r, f_21)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_21, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_27 := calldataload(0x18c4)
                    let a_1 := calldataload(0x1584)
                    let a_14 := calldataload(0x1724)
                    let var7 := mulmod(a_1, a_14, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_27, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_24 := calldataload(0x1ee4)
                    let var0 := 0x1
                    let var1 := sub(r, f_24)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_24, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_28 := calldataload(0x18e4)
                    let a_2 := calldataload(0x15a4)
                    let a_15 := calldataload(0x1744)
                    let var7 := mulmod(a_2, a_15, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_28, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_28 := calldataload(0x1f64)
                    let var0 := 0x2
                    let var1 := sub(r, f_28)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_28, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_29 := calldataload(0x1904)
                    let a_3 := calldataload(0x15c4)
                    let a_16 := calldataload(0x1764)
                    let var7 := mulmod(a_3, a_16, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_29, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_31 := calldataload(0x1fc4)
                    let var0 := 0x1
                    let var1 := sub(r, f_31)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_31, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_30 := calldataload(0x1924)
                    let a_4 := calldataload(0x15e4)
                    let a_17 := calldataload(0x1784)
                    let var7 := mulmod(a_4, a_17, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_30, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_34 := calldataload(0x2024)
                    let var0 := 0x1
                    let var1 := sub(r, f_34)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_34, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_31 := calldataload(0x1944)
                    let a_5 := calldataload(0x1604)
                    let a_18 := calldataload(0x17a4)
                    let var7 := mulmod(a_5, a_18, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_31, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_38 := calldataload(0x20a4)
                    let var0 := 0x2
                    let var1 := sub(r, f_38)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_38, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_32 := calldataload(0x1964)
                    let a_6 := calldataload(0x1624)
                    let a_19 := calldataload(0x17c4)
                    let var7 := mulmod(a_6, a_19, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_32, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_41 := calldataload(0x2104)
                    let var0 := 0x1
                    let var1 := sub(r, f_41)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_41, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_33 := calldataload(0x1984)
                    let a_7 := calldataload(0x1644)
                    let a_20 := calldataload(0x17e4)
                    let var7 := mulmod(a_7, a_20, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_33, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_44 := calldataload(0x2164)
                    let var0 := 0x1
                    let var1 := sub(r, f_44)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_44, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_34 := calldataload(0x19a4)
                    let a_8 := calldataload(0x1664)
                    let a_21 := calldataload(0x1804)
                    let var7 := mulmod(a_8, a_21, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_34, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_48 := calldataload(0x21e4)
                    let var0 := 0x2
                    let var1 := sub(r, f_48)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_48, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_35 := calldataload(0x19c4)
                    let a_9 := calldataload(0x1684)
                    let a_22 := calldataload(0x1824)
                    let var7 := mulmod(a_9, a_22, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_35, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_51 := calldataload(0x2244)
                    let var0 := 0x1
                    let var1 := sub(r, f_51)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_51, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_36 := calldataload(0x19e4)
                    let a_10 := calldataload(0x16a4)
                    let a_23 := calldataload(0x1844)
                    let var7 := mulmod(a_10, a_23, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_36, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_54 := calldataload(0x22a4)
                    let var0 := 0x1
                    let var1 := sub(r, f_54)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_54, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_37 := calldataload(0x1a04)
                    let a_11 := calldataload(0x16c4)
                    let a_24 := calldataload(0x1864)
                    let var7 := mulmod(a_11, a_24, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_37, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_58 := calldataload(0x2324)
                    let var0 := 0x2
                    let var1 := sub(r, f_58)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_58, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_38 := calldataload(0x1a24)
                    let a_12 := calldataload(0x16e4)
                    let a_25 := calldataload(0x1884)
                    let var7 := mulmod(a_12, a_25, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_38, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_16 := calldataload(0x1de4)
                    let var0 := 0x1
                    let var1 := sub(r, f_16)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_16, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_26 := calldataload(0x18a4)
                    let a_0 := calldataload(0x1564)
                    let a_13 := calldataload(0x1704)
                    let var7 := sub(r, a_13)
                    let var8 := addmod(a_0, var7, r)
                    let var9 := sub(r, var8)
                    let var10 := addmod(a_26, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_19 := calldataload(0x1e44)
                    let var0 := 0x1
                    let var1 := sub(r, f_19)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_19, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_27 := calldataload(0x18c4)
                    let a_1 := calldataload(0x1584)
                    let a_14 := calldataload(0x1724)
                    let var7 := sub(r, a_14)
                    let var8 := addmod(a_1, var7, r)
                    let var9 := sub(r, var8)
                    let var10 := addmod(a_27, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_23 := calldataload(0x1ec4)
                    let var0 := 0x2
                    let var1 := sub(r, f_23)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_23, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_28 := calldataload(0x18e4)
                    let a_2 := calldataload(0x15a4)
                    let a_15 := calldataload(0x1744)
                    let var7 := sub(r, a_15)
                    let var8 := addmod(a_2, var7, r)
                    let var9 := sub(r, var8)
                    let var10 := addmod(a_28, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_26 := calldataload(0x1f24)
                    let var0 := 0x1
                    let var1 := sub(r, f_26)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_26, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_29 := calldataload(0x1904)
                    let a_3 := calldataload(0x15c4)
                    let a_16 := calldataload(0x1764)
                    let var7 := sub(r, a_16)
                    let var8 := addmod(a_3, var7, r)
                    let var9 := sub(r, var8)
                    let var10 := addmod(a_29, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_29 := calldataload(0x1f84)
                    let var0 := 0x1
                    let var1 := sub(r, f_29)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_29, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_30 := calldataload(0x1924)
                    let a_4 := calldataload(0x15e4)
                    let a_17 := calldataload(0x1784)
                    let var7 := sub(r, a_17)
                    let var8 := addmod(a_4, var7, r)
                    let var9 := sub(r, var8)
                    let var10 := addmod(a_30, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_33 := calldataload(0x2004)
                    let var0 := 0x2
                    let var1 := sub(r, f_33)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_33, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_31 := calldataload(0x1944)
                    let a_5 := calldataload(0x1604)
                    let a_18 := calldataload(0x17a4)
                    let var7 := sub(r, a_18)
                    let var8 := addmod(a_5, var7, r)
                    let var9 := sub(r, var8)
                    let var10 := addmod(a_31, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_36 := calldataload(0x2064)
                    let var0 := 0x1
                    let var1 := sub(r, f_36)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_36, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_32 := calldataload(0x1964)
                    let a_6 := calldataload(0x1624)
                    let a_19 := calldataload(0x17c4)
                    let var7 := sub(r, a_19)
                    let var8 := addmod(a_6, var7, r)
                    let var9 := sub(r, var8)
                    let var10 := addmod(a_32, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_39 := calldataload(0x20c4)
                    let var0 := 0x1
                    let var1 := sub(r, f_39)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_39, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_33 := calldataload(0x1984)
                    let a_7 := calldataload(0x1644)
                    let a_20 := calldataload(0x17e4)
                    let var7 := sub(r, a_20)
                    let var8 := addmod(a_7, var7, r)
                    let var9 := sub(r, var8)
                    let var10 := addmod(a_33, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_43 := calldataload(0x2144)
                    let var0 := 0x2
                    let var1 := sub(r, f_43)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_43, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_34 := calldataload(0x19a4)
                    let a_8 := calldataload(0x1664)
                    let a_21 := calldataload(0x1804)
                    let var7 := sub(r, a_21)
                    let var8 := addmod(a_8, var7, r)
                    let var9 := sub(r, var8)
                    let var10 := addmod(a_34, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_46 := calldataload(0x21a4)
                    let var0 := 0x1
                    let var1 := sub(r, f_46)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_46, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_35 := calldataload(0x19c4)
                    let a_9 := calldataload(0x1684)
                    let a_22 := calldataload(0x1824)
                    let var7 := sub(r, a_22)
                    let var8 := addmod(a_9, var7, r)
                    let var9 := sub(r, var8)
                    let var10 := addmod(a_35, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_49 := calldataload(0x2204)
                    let var0 := 0x1
                    let var1 := sub(r, f_49)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_49, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_36 := calldataload(0x19e4)
                    let a_10 := calldataload(0x16a4)
                    let a_23 := calldataload(0x1844)
                    let var7 := sub(r, a_23)
                    let var8 := addmod(a_10, var7, r)
                    let var9 := sub(r, var8)
                    let var10 := addmod(a_36, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_53 := calldataload(0x2284)
                    let var0 := 0x2
                    let var1 := sub(r, f_53)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_53, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_37 := calldataload(0x1a04)
                    let a_11 := calldataload(0x16c4)
                    let a_24 := calldataload(0x1864)
                    let var7 := sub(r, a_24)
                    let var8 := addmod(a_11, var7, r)
                    let var9 := sub(r, var8)
                    let var10 := addmod(a_37, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_56 := calldataload(0x22e4)
                    let var0 := 0x1
                    let var1 := sub(r, f_56)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_56, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_38 := calldataload(0x1a24)
                    let a_12 := calldataload(0x16e4)
                    let a_25 := calldataload(0x1884)
                    let var7 := sub(r, a_25)
                    let var8 := addmod(a_12, var7, r)
                    let var9 := sub(r, var8)
                    let var10 := addmod(a_38, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_17 := calldataload(0x1e04)
                    let var0 := 0x1
                    let var1 := sub(r, f_17)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_17, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_26 := calldataload(0x18a4)
                    let a_13 := calldataload(0x1704)
                    let a_26_prev_1 := calldataload(0x1a44)
                    let var7 := addmod(a_13, a_26_prev_1, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_26, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_20 := calldataload(0x1e64)
                    let var0 := 0x1
                    let var1 := sub(r, f_20)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_20, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_27 := calldataload(0x18c4)
                    let a_14 := calldataload(0x1724)
                    let a_27_prev_1 := calldataload(0x1a64)
                    let var7 := addmod(a_14, a_27_prev_1, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_27, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_24 := calldataload(0x1ee4)
                    let var0 := 0x2
                    let var1 := sub(r, f_24)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_24, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_28 := calldataload(0x18e4)
                    let a_15 := calldataload(0x1744)
                    let a_28_prev_1 := calldataload(0x1a84)
                    let var7 := addmod(a_15, a_28_prev_1, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_28, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_27 := calldataload(0x1f44)
                    let var0 := 0x1
                    let var1 := sub(r, f_27)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_27, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_29 := calldataload(0x1904)
                    let a_16 := calldataload(0x1764)
                    let a_29_prev_1 := calldataload(0x1aa4)
                    let var7 := addmod(a_16, a_29_prev_1, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_29, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_30 := calldataload(0x1fa4)
                    let var0 := 0x1
                    let var1 := sub(r, f_30)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_30, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_30 := calldataload(0x1924)
                    let a_17 := calldataload(0x1784)
                    let a_30_prev_1 := calldataload(0x1ac4)
                    let var7 := addmod(a_17, a_30_prev_1, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_30, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_34 := calldataload(0x2024)
                    let var0 := 0x2
                    let var1 := sub(r, f_34)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_34, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_31 := calldataload(0x1944)
                    let a_18 := calldataload(0x17a4)
                    let a_31_prev_1 := calldataload(0x1ae4)
                    let var7 := addmod(a_18, a_31_prev_1, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_31, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_37 := calldataload(0x2084)
                    let var0 := 0x1
                    let var1 := sub(r, f_37)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_37, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_32 := calldataload(0x1964)
                    let a_19 := calldataload(0x17c4)
                    let a_32_prev_1 := calldataload(0x1b04)
                    let var7 := addmod(a_19, a_32_prev_1, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_32, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_40 := calldataload(0x20e4)
                    let var0 := 0x1
                    let var1 := sub(r, f_40)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_40, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_33 := calldataload(0x1984)
                    let a_20 := calldataload(0x17e4)
                    let a_33_prev_1 := calldataload(0x1b24)
                    let var7 := addmod(a_20, a_33_prev_1, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_33, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_44 := calldataload(0x2164)
                    let var0 := 0x2
                    let var1 := sub(r, f_44)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_44, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_34 := calldataload(0x19a4)
                    let a_21 := calldataload(0x1804)
                    let a_34_prev_1 := calldataload(0x1b44)
                    let var7 := addmod(a_21, a_34_prev_1, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_34, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_47 := calldataload(0x21c4)
                    let var0 := 0x1
                    let var1 := sub(r, f_47)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_47, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_35 := calldataload(0x19c4)
                    let a_22 := calldataload(0x1824)
                    let a_35_prev_1 := calldataload(0x1b64)
                    let var7 := addmod(a_22, a_35_prev_1, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_35, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_50 := calldataload(0x2224)
                    let var0 := 0x1
                    let var1 := sub(r, f_50)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_50, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_36 := calldataload(0x19e4)
                    let a_23 := calldataload(0x1844)
                    let a_36_prev_1 := calldataload(0x1b84)
                    let var7 := addmod(a_23, a_36_prev_1, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_36, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_54 := calldataload(0x22a4)
                    let var0 := 0x2
                    let var1 := sub(r, f_54)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_54, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_37 := calldataload(0x1a04)
                    let a_24 := calldataload(0x1864)
                    let a_37_prev_1 := calldataload(0x1ba4)
                    let var7 := addmod(a_24, a_37_prev_1, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_37, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_57 := calldataload(0x2304)
                    let var0 := 0x1
                    let var1 := sub(r, f_57)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_57, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_38 := calldataload(0x1a24)
                    let a_25 := calldataload(0x1884)
                    let a_38_prev_1 := calldataload(0x1bc4)
                    let var7 := addmod(a_25, a_38_prev_1, r)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_38, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_17 := calldataload(0x1e04)
                    let var0 := 0x1
                    let var1 := sub(r, f_17)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_17, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_26 := calldataload(0x18a4)
                    let a_13 := calldataload(0x1704)
                    let var7 := sub(r, a_13)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_26, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_21 := calldataload(0x1e84)
                    let var0 := 0x2
                    let var1 := sub(r, f_21)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_21, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_27 := calldataload(0x18c4)
                    let a_14 := calldataload(0x1724)
                    let var7 := sub(r, a_14)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_27, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_24 := calldataload(0x1ee4)
                    let var0 := 0x1
                    let var1 := sub(r, f_24)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_24, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_28 := calldataload(0x18e4)
                    let a_15 := calldataload(0x1744)
                    let var7 := sub(r, a_15)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_28, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_27 := calldataload(0x1f44)
                    let var0 := 0x1
                    let var1 := sub(r, f_27)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_27, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_29 := calldataload(0x1904)
                    let a_16 := calldataload(0x1764)
                    let var7 := sub(r, a_16)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_29, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_31 := calldataload(0x1fc4)
                    let var0 := 0x2
                    let var1 := sub(r, f_31)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_31, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_30 := calldataload(0x1924)
                    let a_17 := calldataload(0x1784)
                    let var7 := sub(r, a_17)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_30, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_34 := calldataload(0x2024)
                    let var0 := 0x1
                    let var1 := sub(r, f_34)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_34, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_31 := calldataload(0x1944)
                    let a_18 := calldataload(0x17a4)
                    let var7 := sub(r, a_18)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_31, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_37 := calldataload(0x2084)
                    let var0 := 0x1
                    let var1 := sub(r, f_37)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_37, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_32 := calldataload(0x1964)
                    let a_19 := calldataload(0x17c4)
                    let var7 := sub(r, a_19)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_32, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_41 := calldataload(0x2104)
                    let var0 := 0x2
                    let var1 := sub(r, f_41)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_41, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_33 := calldataload(0x1984)
                    let a_20 := calldataload(0x17e4)
                    let var7 := sub(r, a_20)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_33, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_44 := calldataload(0x2164)
                    let var0 := 0x1
                    let var1 := sub(r, f_44)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_44, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_34 := calldataload(0x19a4)
                    let a_21 := calldataload(0x1804)
                    let var7 := sub(r, a_21)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_34, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_47 := calldataload(0x21c4)
                    let var0 := 0x1
                    let var1 := sub(r, f_47)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_47, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_35 := calldataload(0x19c4)
                    let a_22 := calldataload(0x1824)
                    let var7 := sub(r, a_22)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_35, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_51 := calldataload(0x2244)
                    let var0 := 0x2
                    let var1 := sub(r, f_51)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_51, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_36 := calldataload(0x19e4)
                    let a_23 := calldataload(0x1844)
                    let var7 := sub(r, a_23)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_36, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_54 := calldataload(0x22a4)
                    let var0 := 0x1
                    let var1 := sub(r, f_54)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_54, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_37 := calldataload(0x1a04)
                    let a_24 := calldataload(0x1864)
                    let var7 := sub(r, a_24)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_37, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_57 := calldataload(0x2304)
                    let var0 := 0x1
                    let var1 := sub(r, f_57)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_57, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_38 := calldataload(0x1a24)
                    let a_25 := calldataload(0x1884)
                    let var7 := sub(r, a_25)
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_38, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_18 := calldataload(0x1e24)
                    let var0 := 0x1
                    let var1 := sub(r, f_18)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_18, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_13 := calldataload(0x1704)
                    let var7 := mulmod(var6, a_13, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var7, r)
                }
                {
                    let f_21 := calldataload(0x1e84)
                    let var0 := 0x1
                    let var1 := sub(r, f_21)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_21, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_14 := calldataload(0x1724)
                    let var7 := mulmod(var6, a_14, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var7, r)
                }
                {
                    let f_25 := calldataload(0x1f04)
                    let var0 := 0x2
                    let var1 := sub(r, f_25)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_25, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_15 := calldataload(0x1744)
                    let var7 := mulmod(var6, a_15, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var7, r)
                }
                {
                    let f_28 := calldataload(0x1f64)
                    let var0 := 0x1
                    let var1 := sub(r, f_28)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_28, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_16 := calldataload(0x1764)
                    let var7 := mulmod(var6, a_16, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var7, r)
                }
                {
                    let f_31 := calldataload(0x1fc4)
                    let var0 := 0x1
                    let var1 := sub(r, f_31)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_31, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_17 := calldataload(0x1784)
                    let var7 := mulmod(var6, a_17, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var7, r)
                }
                {
                    let f_35 := calldataload(0x2044)
                    let var0 := 0x2
                    let var1 := sub(r, f_35)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_35, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_18 := calldataload(0x17a4)
                    let var7 := mulmod(var6, a_18, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var7, r)
                }
                {
                    let f_38 := calldataload(0x20a4)
                    let var0 := 0x1
                    let var1 := sub(r, f_38)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_38, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_19 := calldataload(0x17c4)
                    let var7 := mulmod(var6, a_19, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var7, r)
                }
                {
                    let f_41 := calldataload(0x2104)
                    let var0 := 0x1
                    let var1 := sub(r, f_41)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_41, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_20 := calldataload(0x17e4)
                    let var7 := mulmod(var6, a_20, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var7, r)
                }
                {
                    let f_45 := calldataload(0x2184)
                    let var0 := 0x2
                    let var1 := sub(r, f_45)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_45, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_21 := calldataload(0x1804)
                    let var7 := mulmod(var6, a_21, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var7, r)
                }
                {
                    let f_48 := calldataload(0x21e4)
                    let var0 := 0x1
                    let var1 := sub(r, f_48)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_48, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_22 := calldataload(0x1824)
                    let var7 := mulmod(var6, a_22, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var7, r)
                }
                {
                    let f_51 := calldataload(0x2244)
                    let var0 := 0x1
                    let var1 := sub(r, f_51)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_51, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_23 := calldataload(0x1844)
                    let var7 := mulmod(var6, a_23, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var7, r)
                }
                {
                    let f_55 := calldataload(0x22c4)
                    let var0 := 0x2
                    let var1 := sub(r, f_55)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_55, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_24 := calldataload(0x1864)
                    let var7 := mulmod(var6, a_24, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var7, r)
                }
                {
                    let f_58 := calldataload(0x2324)
                    let var0 := 0x1
                    let var1 := sub(r, f_58)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_58, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_25 := calldataload(0x1884)
                    let var7 := mulmod(var6, a_25, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var7, r)
                }
                {
                    let f_19 := calldataload(0x1e44)
                    let var0 := 0x2
                    let var1 := sub(r, f_19)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_19, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_13 := calldataload(0x1704)
                    let var7 := 0x1
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_13, var8, r)
                    let var10 := mulmod(a_13, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_22 := calldataload(0x1ea4)
                    let var0 := 0x1
                    let var1 := sub(r, f_22)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_22, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_14 := calldataload(0x1724)
                    let var7 := sub(r, var0)
                    let var8 := addmod(a_14, var7, r)
                    let var9 := mulmod(a_14, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_25 := calldataload(0x1f04)
                    let var0 := 0x1
                    let var1 := sub(r, f_25)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_25, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_15 := calldataload(0x1744)
                    let var7 := sub(r, var0)
                    let var8 := addmod(a_15, var7, r)
                    let var9 := mulmod(a_15, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_29 := calldataload(0x1f84)
                    let var0 := 0x2
                    let var1 := sub(r, f_29)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_29, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_16 := calldataload(0x1764)
                    let var7 := 0x1
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_16, var8, r)
                    let var10 := mulmod(a_16, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_32 := calldataload(0x1fe4)
                    let var0 := 0x1
                    let var1 := sub(r, f_32)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_32, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_17 := calldataload(0x1784)
                    let var7 := sub(r, var0)
                    let var8 := addmod(a_17, var7, r)
                    let var9 := mulmod(a_17, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_35 := calldataload(0x2044)
                    let var0 := 0x1
                    let var1 := sub(r, f_35)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_35, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_18 := calldataload(0x17a4)
                    let var7 := sub(r, var0)
                    let var8 := addmod(a_18, var7, r)
                    let var9 := mulmod(a_18, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_39 := calldataload(0x20c4)
                    let var0 := 0x2
                    let var1 := sub(r, f_39)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_39, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_19 := calldataload(0x17c4)
                    let var7 := 0x1
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_19, var8, r)
                    let var10 := mulmod(a_19, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_42 := calldataload(0x2124)
                    let var0 := 0x1
                    let var1 := sub(r, f_42)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_42, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_20 := calldataload(0x17e4)
                    let var7 := sub(r, var0)
                    let var8 := addmod(a_20, var7, r)
                    let var9 := mulmod(a_20, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_45 := calldataload(0x2184)
                    let var0 := 0x1
                    let var1 := sub(r, f_45)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_45, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_21 := calldataload(0x1804)
                    let var7 := sub(r, var0)
                    let var8 := addmod(a_21, var7, r)
                    let var9 := mulmod(a_21, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_49 := calldataload(0x2204)
                    let var0 := 0x2
                    let var1 := sub(r, f_49)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_49, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_22 := calldataload(0x1824)
                    let var7 := 0x1
                    let var8 := sub(r, var7)
                    let var9 := addmod(a_22, var8, r)
                    let var10 := mulmod(a_22, var9, r)
                    let var11 := mulmod(var6, var10, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_52 := calldataload(0x2264)
                    let var0 := 0x1
                    let var1 := sub(r, f_52)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_52, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_23 := calldataload(0x1844)
                    let var7 := sub(r, var0)
                    let var8 := addmod(a_23, var7, r)
                    let var9 := mulmod(a_23, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_55 := calldataload(0x22c4)
                    let var0 := 0x1
                    let var1 := sub(r, f_55)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_55, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_24 := calldataload(0x1864)
                    let var7 := sub(r, var0)
                    let var8 := addmod(a_24, var7, r)
                    let var9 := mulmod(a_24, var8, r)
                    let var10 := mulmod(var6, var9, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_59 := calldataload(0x2344)
                    let a_25 := calldataload(0x1884)
                    let var0 := 0x1
                    let var1 := sub(r, var0)
                    let var2 := addmod(a_25, var1, r)
                    let var3 := mulmod(a_25, var2, r)
                    let var4 := mulmod(f_59, var3, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var4, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := addmod(l_0, sub(r, mulmod(l_0, calldataload(0x28a4), r)), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let perm_z_last := calldataload(0x2d84)
                    let eval := mulmod(mload(L_LAST_MPTR), addmod(mulmod(perm_z_last, perm_z_last, r), sub(r, perm_z_last), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x2904), sub(r, calldataload(0x28e4)), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x2964), sub(r, calldataload(0x2944)), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x29c4), sub(r, calldataload(0x29a4)), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x2a24), sub(r, calldataload(0x2a04)), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x2a84), sub(r, calldataload(0x2a64)), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x2ae4), sub(r, calldataload(0x2ac4)), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x2b44), sub(r, calldataload(0x2b24)), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x2ba4), sub(r, calldataload(0x2b84)), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x2c04), sub(r, calldataload(0x2be4)), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x2c64), sub(r, calldataload(0x2c44)), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x2cc4), sub(r, calldataload(0x2ca4)), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x2d24), sub(r, calldataload(0x2d04)), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x2d84), sub(r, calldataload(0x2d64)), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x28c4)
                    let rhs := calldataload(0x28a4)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x1564), mulmod(beta, calldataload(0x2384), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x1584), mulmod(beta, calldataload(0x23a4), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x15a4), mulmod(beta, calldataload(0x23c4), r), r), gamma, r), r)
                    mstore(0x00, mulmod(beta, mload(X_MPTR), r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x1564), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x1584), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x15a4), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    let left_sub_right := addmod(lhs, sub(r, rhs), r)
                    let eval := addmod(left_sub_right, sub(r, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), r), r)), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x2924)
                    let rhs := calldataload(0x2904)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x15c4), mulmod(beta, calldataload(0x23e4), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x15e4), mulmod(beta, calldataload(0x2404), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x1604), mulmod(beta, calldataload(0x2424), r), r), gamma, r), r)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x15c4), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x15e4), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x1604), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    let left_sub_right := addmod(lhs, sub(r, rhs), r)
                    let eval := addmod(left_sub_right, sub(r, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), r), r)), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x2984)
                    let rhs := calldataload(0x2964)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x1624), mulmod(beta, calldataload(0x2444), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x1644), mulmod(beta, calldataload(0x2464), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x1664), mulmod(beta, calldataload(0x2484), r), r), gamma, r), r)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x1624), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x1644), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x1664), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    let left_sub_right := addmod(lhs, sub(r, rhs), r)
                    let eval := addmod(left_sub_right, sub(r, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), r), r)), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x29e4)
                    let rhs := calldataload(0x29c4)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x1684), mulmod(beta, calldataload(0x24a4), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x16a4), mulmod(beta, calldataload(0x24c4), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x16c4), mulmod(beta, calldataload(0x24e4), r), r), gamma, r), r)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x1684), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x16a4), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x16c4), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    let left_sub_right := addmod(lhs, sub(r, rhs), r)
                    let eval := addmod(left_sub_right, sub(r, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), r), r)), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x2a44)
                    let rhs := calldataload(0x2a24)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x16e4), mulmod(beta, calldataload(0x2504), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x1704), mulmod(beta, calldataload(0x2524), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x1724), mulmod(beta, calldataload(0x2544), r), r), gamma, r), r)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x16e4), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x1704), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x1724), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    let left_sub_right := addmod(lhs, sub(r, rhs), r)
                    let eval := addmod(left_sub_right, sub(r, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), r), r)), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x2aa4)
                    let rhs := calldataload(0x2a84)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x1744), mulmod(beta, calldataload(0x2564), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x1764), mulmod(beta, calldataload(0x2584), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x1784), mulmod(beta, calldataload(0x25a4), r), r), gamma, r), r)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x1744), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x1764), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x1784), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    let left_sub_right := addmod(lhs, sub(r, rhs), r)
                    let eval := addmod(left_sub_right, sub(r, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), r), r)), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x2b04)
                    let rhs := calldataload(0x2ae4)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x17a4), mulmod(beta, calldataload(0x25c4), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x17c4), mulmod(beta, calldataload(0x25e4), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x17e4), mulmod(beta, calldataload(0x2604), r), r), gamma, r), r)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x17a4), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x17c4), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x17e4), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    let left_sub_right := addmod(lhs, sub(r, rhs), r)
                    let eval := addmod(left_sub_right, sub(r, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), r), r)), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x2b64)
                    let rhs := calldataload(0x2b44)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x1804), mulmod(beta, calldataload(0x2624), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x1824), mulmod(beta, calldataload(0x2644), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x1844), mulmod(beta, calldataload(0x2664), r), r), gamma, r), r)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x1804), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x1824), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x1844), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    let left_sub_right := addmod(lhs, sub(r, rhs), r)
                    let eval := addmod(left_sub_right, sub(r, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), r), r)), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x2bc4)
                    let rhs := calldataload(0x2ba4)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x1864), mulmod(beta, calldataload(0x2684), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x1884), mulmod(beta, calldataload(0x26a4), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x18a4), mulmod(beta, calldataload(0x26c4), r), r), gamma, r), r)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x1864), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x1884), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x18a4), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    let left_sub_right := addmod(lhs, sub(r, rhs), r)
                    let eval := addmod(left_sub_right, sub(r, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), r), r)), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x2c24)
                    let rhs := calldataload(0x2c04)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x18c4), mulmod(beta, calldataload(0x26e4), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x18e4), mulmod(beta, calldataload(0x2704), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x1904), mulmod(beta, calldataload(0x2724), r), r), gamma, r), r)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x18c4), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x18e4), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x1904), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    let left_sub_right := addmod(lhs, sub(r, rhs), r)
                    let eval := addmod(left_sub_right, sub(r, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), r), r)), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x2c84)
                    let rhs := calldataload(0x2c64)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x1924), mulmod(beta, calldataload(0x2744), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x1944), mulmod(beta, calldataload(0x2764), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x1964), mulmod(beta, calldataload(0x2784), r), r), gamma, r), r)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x1924), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x1944), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x1964), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    let left_sub_right := addmod(lhs, sub(r, rhs), r)
                    let eval := addmod(left_sub_right, sub(r, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), r), r)), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x2ce4)
                    let rhs := calldataload(0x2cc4)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x1984), mulmod(beta, calldataload(0x27a4), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x19a4), mulmod(beta, calldataload(0x27c4), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x19c4), mulmod(beta, calldataload(0x27e4), r), r), gamma, r), r)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x1984), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x19a4), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x19c4), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    let left_sub_right := addmod(lhs, sub(r, rhs), r)
                    let eval := addmod(left_sub_right, sub(r, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), r), r)), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x2d44)
                    let rhs := calldataload(0x2d24)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x19e4), mulmod(beta, calldataload(0x2804), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x1a04), mulmod(beta, calldataload(0x2824), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x1a24), mulmod(beta, calldataload(0x2844), r), r), gamma, r), r)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x19e4), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x1a04), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x1a24), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    let left_sub_right := addmod(lhs, sub(r, rhs), r)
                    let eval := addmod(left_sub_right, sub(r, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), r), r)), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x2da4)
                    let rhs := calldataload(0x2d84)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x1be4), mulmod(beta, calldataload(0x2864), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(mload(INSTANCE_EVAL_MPTR), mulmod(beta, calldataload(0x2884), r), r), gamma, r), r)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x1be4), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(mload(INSTANCE_EVAL_MPTR), mload(0x00), r), gamma, r), r)
                    let left_sub_right := addmod(lhs, sub(r, rhs), r)
                    let eval := addmod(left_sub_right, sub(r, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), r), r)), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x2dc4), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x2dc4), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x1c04)
                        let f_2 := calldataload(0x1c24)
                        table := f_1
                        table := addmod(mulmod(table, theta, r), f_2, r)
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let f_3 := calldataload(0x1c44)
                        let var0 := 0x1
                        let var1 := mulmod(f_3, var0, r)
                        let a_0 := calldataload(0x1564)
                        let var2 := mulmod(var1, a_0, r)
                        let var3 := sub(r, var1)
                        let var4 := addmod(var0, var3, r)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effff899
                        let var6 := mulmod(var4, var5, r)
                        let var7 := addmod(var2, var6, r)
                        let a_13 := calldataload(0x1704)
                        let var8 := mulmod(var1, a_13, r)
                        let var9 := 0x0
                        let var10 := mulmod(var4, var9, r)
                        let var11 := addmod(var8, var10, r)
                        input_0 := var7
                        input_0 := addmod(mulmod(input_0, theta, r), var11, r)
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x2e04), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x2de4), sub(r, calldataload(0x2dc4)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x2e24), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x2e24), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x1c04)
                        let f_2 := calldataload(0x1c24)
                        table := f_1
                        table := addmod(mulmod(table, theta, r), f_2, r)
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let f_4 := calldataload(0x1c64)
                        let var0 := 0x1
                        let var1 := mulmod(f_4, var0, r)
                        let a_1 := calldataload(0x1584)
                        let var2 := mulmod(var1, a_1, r)
                        let var3 := sub(r, var1)
                        let var4 := addmod(var0, var3, r)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effff899
                        let var6 := mulmod(var4, var5, r)
                        let var7 := addmod(var2, var6, r)
                        let a_14 := calldataload(0x1724)
                        let var8 := mulmod(var1, a_14, r)
                        let var9 := 0x0
                        let var10 := mulmod(var4, var9, r)
                        let var11 := addmod(var8, var10, r)
                        input_0 := var7
                        input_0 := addmod(mulmod(input_0, theta, r), var11, r)
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x2e64), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x2e44), sub(r, calldataload(0x2e24)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x2e84), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x2e84), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x1c04)
                        let f_2 := calldataload(0x1c24)
                        table := f_1
                        table := addmod(mulmod(table, theta, r), f_2, r)
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let f_5 := calldataload(0x1c84)
                        let var0 := 0x1
                        let var1 := mulmod(f_5, var0, r)
                        let a_2 := calldataload(0x15a4)
                        let var2 := mulmod(var1, a_2, r)
                        let var3 := sub(r, var1)
                        let var4 := addmod(var0, var3, r)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effff899
                        let var6 := mulmod(var4, var5, r)
                        let var7 := addmod(var2, var6, r)
                        let a_15 := calldataload(0x1744)
                        let var8 := mulmod(var1, a_15, r)
                        let var9 := 0x0
                        let var10 := mulmod(var4, var9, r)
                        let var11 := addmod(var8, var10, r)
                        input_0 := var7
                        input_0 := addmod(mulmod(input_0, theta, r), var11, r)
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x2ec4), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x2ea4), sub(r, calldataload(0x2e84)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x2ee4), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x2ee4), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x1c04)
                        let f_2 := calldataload(0x1c24)
                        table := f_1
                        table := addmod(mulmod(table, theta, r), f_2, r)
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let f_6 := calldataload(0x1ca4)
                        let var0 := 0x1
                        let var1 := mulmod(f_6, var0, r)
                        let a_3 := calldataload(0x15c4)
                        let var2 := mulmod(var1, a_3, r)
                        let var3 := sub(r, var1)
                        let var4 := addmod(var0, var3, r)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effff899
                        let var6 := mulmod(var4, var5, r)
                        let var7 := addmod(var2, var6, r)
                        let a_16 := calldataload(0x1764)
                        let var8 := mulmod(var1, a_16, r)
                        let var9 := 0x0
                        let var10 := mulmod(var4, var9, r)
                        let var11 := addmod(var8, var10, r)
                        input_0 := var7
                        input_0 := addmod(mulmod(input_0, theta, r), var11, r)
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x2f24), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x2f04), sub(r, calldataload(0x2ee4)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x2f44), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x2f44), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x1c04)
                        let f_2 := calldataload(0x1c24)
                        table := f_1
                        table := addmod(mulmod(table, theta, r), f_2, r)
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let f_7 := calldataload(0x1cc4)
                        let var0 := 0x1
                        let var1 := mulmod(f_7, var0, r)
                        let a_4 := calldataload(0x15e4)
                        let var2 := mulmod(var1, a_4, r)
                        let var3 := sub(r, var1)
                        let var4 := addmod(var0, var3, r)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effff899
                        let var6 := mulmod(var4, var5, r)
                        let var7 := addmod(var2, var6, r)
                        let a_17 := calldataload(0x1784)
                        let var8 := mulmod(var1, a_17, r)
                        let var9 := 0x0
                        let var10 := mulmod(var4, var9, r)
                        let var11 := addmod(var8, var10, r)
                        input_0 := var7
                        input_0 := addmod(mulmod(input_0, theta, r), var11, r)
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x2f84), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x2f64), sub(r, calldataload(0x2f44)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x2fa4), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x2fa4), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x1c04)
                        let f_2 := calldataload(0x1c24)
                        table := f_1
                        table := addmod(mulmod(table, theta, r), f_2, r)
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let f_8 := calldataload(0x1ce4)
                        let var0 := 0x1
                        let var1 := mulmod(f_8, var0, r)
                        let a_5 := calldataload(0x1604)
                        let var2 := mulmod(var1, a_5, r)
                        let var3 := sub(r, var1)
                        let var4 := addmod(var0, var3, r)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effff899
                        let var6 := mulmod(var4, var5, r)
                        let var7 := addmod(var2, var6, r)
                        let a_18 := calldataload(0x17a4)
                        let var8 := mulmod(var1, a_18, r)
                        let var9 := 0x0
                        let var10 := mulmod(var4, var9, r)
                        let var11 := addmod(var8, var10, r)
                        input_0 := var7
                        input_0 := addmod(mulmod(input_0, theta, r), var11, r)
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x2fe4), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x2fc4), sub(r, calldataload(0x2fa4)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x3004), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x3004), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x1c04)
                        let f_2 := calldataload(0x1c24)
                        table := f_1
                        table := addmod(mulmod(table, theta, r), f_2, r)
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let f_9 := calldataload(0x1d04)
                        let var0 := 0x1
                        let var1 := mulmod(f_9, var0, r)
                        let a_6 := calldataload(0x1624)
                        let var2 := mulmod(var1, a_6, r)
                        let var3 := sub(r, var1)
                        let var4 := addmod(var0, var3, r)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effff899
                        let var6 := mulmod(var4, var5, r)
                        let var7 := addmod(var2, var6, r)
                        let a_19 := calldataload(0x17c4)
                        let var8 := mulmod(var1, a_19, r)
                        let var9 := 0x0
                        let var10 := mulmod(var4, var9, r)
                        let var11 := addmod(var8, var10, r)
                        input_0 := var7
                        input_0 := addmod(mulmod(input_0, theta, r), var11, r)
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x3044), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x3024), sub(r, calldataload(0x3004)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x3064), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x3064), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x1c04)
                        let f_2 := calldataload(0x1c24)
                        table := f_1
                        table := addmod(mulmod(table, theta, r), f_2, r)
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let f_10 := calldataload(0x1d24)
                        let var0 := 0x1
                        let var1 := mulmod(f_10, var0, r)
                        let a_7 := calldataload(0x1644)
                        let var2 := mulmod(var1, a_7, r)
                        let var3 := sub(r, var1)
                        let var4 := addmod(var0, var3, r)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effff899
                        let var6 := mulmod(var4, var5, r)
                        let var7 := addmod(var2, var6, r)
                        let a_20 := calldataload(0x17e4)
                        let var8 := mulmod(var1, a_20, r)
                        let var9 := 0x0
                        let var10 := mulmod(var4, var9, r)
                        let var11 := addmod(var8, var10, r)
                        input_0 := var7
                        input_0 := addmod(mulmod(input_0, theta, r), var11, r)
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x30a4), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x3084), sub(r, calldataload(0x3064)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x30c4), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x30c4), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x1c04)
                        let f_2 := calldataload(0x1c24)
                        table := f_1
                        table := addmod(mulmod(table, theta, r), f_2, r)
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let f_11 := calldataload(0x1d44)
                        let var0 := 0x1
                        let var1 := mulmod(f_11, var0, r)
                        let a_8 := calldataload(0x1664)
                        let var2 := mulmod(var1, a_8, r)
                        let var3 := sub(r, var1)
                        let var4 := addmod(var0, var3, r)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effff899
                        let var6 := mulmod(var4, var5, r)
                        let var7 := addmod(var2, var6, r)
                        let a_21 := calldataload(0x1804)
                        let var8 := mulmod(var1, a_21, r)
                        let var9 := 0x0
                        let var10 := mulmod(var4, var9, r)
                        let var11 := addmod(var8, var10, r)
                        input_0 := var7
                        input_0 := addmod(mulmod(input_0, theta, r), var11, r)
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x3104), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x30e4), sub(r, calldataload(0x30c4)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x3124), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x3124), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x1c04)
                        let f_2 := calldataload(0x1c24)
                        table := f_1
                        table := addmod(mulmod(table, theta, r), f_2, r)
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let f_12 := calldataload(0x1d64)
                        let var0 := 0x1
                        let var1 := mulmod(f_12, var0, r)
                        let a_9 := calldataload(0x1684)
                        let var2 := mulmod(var1, a_9, r)
                        let var3 := sub(r, var1)
                        let var4 := addmod(var0, var3, r)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effff899
                        let var6 := mulmod(var4, var5, r)
                        let var7 := addmod(var2, var6, r)
                        let a_22 := calldataload(0x1824)
                        let var8 := mulmod(var1, a_22, r)
                        let var9 := 0x0
                        let var10 := mulmod(var4, var9, r)
                        let var11 := addmod(var8, var10, r)
                        input_0 := var7
                        input_0 := addmod(mulmod(input_0, theta, r), var11, r)
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x3164), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x3144), sub(r, calldataload(0x3124)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x3184), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x3184), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x1c04)
                        let f_2 := calldataload(0x1c24)
                        table := f_1
                        table := addmod(mulmod(table, theta, r), f_2, r)
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let f_13 := calldataload(0x1d84)
                        let var0 := 0x1
                        let var1 := mulmod(f_13, var0, r)
                        let a_10 := calldataload(0x16a4)
                        let var2 := mulmod(var1, a_10, r)
                        let var3 := sub(r, var1)
                        let var4 := addmod(var0, var3, r)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effff899
                        let var6 := mulmod(var4, var5, r)
                        let var7 := addmod(var2, var6, r)
                        let a_23 := calldataload(0x1844)
                        let var8 := mulmod(var1, a_23, r)
                        let var9 := 0x0
                        let var10 := mulmod(var4, var9, r)
                        let var11 := addmod(var8, var10, r)
                        input_0 := var7
                        input_0 := addmod(mulmod(input_0, theta, r), var11, r)
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x31c4), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x31a4), sub(r, calldataload(0x3184)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x31e4), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x31e4), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x1c04)
                        let f_2 := calldataload(0x1c24)
                        table := f_1
                        table := addmod(mulmod(table, theta, r), f_2, r)
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let f_14 := calldataload(0x1da4)
                        let var0 := 0x1
                        let var1 := mulmod(f_14, var0, r)
                        let a_11 := calldataload(0x16c4)
                        let var2 := mulmod(var1, a_11, r)
                        let var3 := sub(r, var1)
                        let var4 := addmod(var0, var3, r)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effff899
                        let var6 := mulmod(var4, var5, r)
                        let var7 := addmod(var2, var6, r)
                        let a_24 := calldataload(0x1864)
                        let var8 := mulmod(var1, a_24, r)
                        let var9 := 0x0
                        let var10 := mulmod(var4, var9, r)
                        let var11 := addmod(var8, var10, r)
                        input_0 := var7
                        input_0 := addmod(mulmod(input_0, theta, r), var11, r)
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x3224), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x3204), sub(r, calldataload(0x31e4)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x3244), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x3244), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x1c04)
                        let f_2 := calldataload(0x1c24)
                        table := f_1
                        table := addmod(mulmod(table, theta, r), f_2, r)
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let f_15 := calldataload(0x1dc4)
                        let var0 := 0x1
                        let var1 := mulmod(f_15, var0, r)
                        let a_12 := calldataload(0x16e4)
                        let var2 := mulmod(var1, a_12, r)
                        let var3 := sub(r, var1)
                        let var4 := addmod(var0, var3, r)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effff899
                        let var6 := mulmod(var4, var5, r)
                        let var7 := addmod(var2, var6, r)
                        let a_25 := calldataload(0x1884)
                        let var8 := mulmod(var1, a_25, r)
                        let var9 := 0x0
                        let var10 := mulmod(var4, var9, r)
                        let var11 := addmod(var8, var10, r)
                        input_0 := var7
                        input_0 := addmod(mulmod(input_0, theta, r), var11, r)
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x3284), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x3264), sub(r, calldataload(0x3244)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }

                pop(y)
                pop(delta)

                let quotient_eval := mulmod(quotient_eval_numer, mload(X_N_MINUS_1_INV_MPTR), r)
                mstore(QUOTIENT_EVAL_MPTR, quotient_eval)
            }

            // Compute quotient commitment
            {
                mstore(0x00, calldataload(LAST_QUOTIENT_X_CPTR))
                mstore(0x20, calldataload(add(LAST_QUOTIENT_X_CPTR, 0x20)))
                let x_n := mload(X_N_MPTR)
                for
                    {
                        let cptr := sub(LAST_QUOTIENT_X_CPTR, 0x40)
                        let cptr_end := sub(FIRST_QUOTIENT_X_CPTR, 0x40)
                    }
                    lt(cptr_end, cptr)
                    {}
                {
                    success := ec_mul_acc(success, x_n)
                    success := ec_add_acc(success, calldataload(cptr), calldataload(add(cptr, 0x20)))
                    cptr := sub(cptr, 0x40)
                }
                mstore(QUOTIENT_X_MPTR, mload(0x00))
                mstore(QUOTIENT_Y_MPTR, mload(0x20))
            }

            // Compute pairing lhs and rhs
            {
                {
                    let x := mload(X_MPTR)
                    let omega := mload(OMEGA_MPTR)
                    let omega_inv := mload(OMEGA_INV_MPTR)
                    let x_pow_of_omega := mulmod(x, omega, r)
                    mstore(0x0360, x_pow_of_omega)
                    mstore(0x0340, x)
                    x_pow_of_omega := mulmod(x, omega_inv, r)
                    mstore(0x0320, x_pow_of_omega)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)
                    mstore(0x0300, x_pow_of_omega)
                }
                {
                    let mu := mload(MU_MPTR)
                    for
                        {
                            let mptr := 0x0380
                            let mptr_end := 0x0400
                            let point_mptr := 0x0300
                        }
                        lt(mptr, mptr_end)
                        {
                            mptr := add(mptr, 0x20)
                            point_mptr := add(point_mptr, 0x20)
                        }
                    {
                        mstore(mptr, addmod(mu, sub(r, mload(point_mptr)), r))
                    }
                    let s
                    s := mload(0x03c0)
                    mstore(0x0400, s)
                    let diff
                    diff := mload(0x0380)
                    diff := mulmod(diff, mload(0x03a0), r)
                    diff := mulmod(diff, mload(0x03e0), r)
                    mstore(0x0420, diff)
                    mstore(0x00, diff)
                    diff := mload(0x0380)
                    diff := mulmod(diff, mload(0x03e0), r)
                    mstore(0x0440, diff)
                    diff := mload(0x03a0)
                    mstore(0x0460, diff)
                    diff := mload(0x0380)
                    diff := mulmod(diff, mload(0x03a0), r)
                    mstore(0x0480, diff)
                }
                {
                    let point_2 := mload(0x0340)
                    let coeff
                    coeff := 1
                    coeff := mulmod(coeff, mload(0x03c0), r)
                    mstore(0x20, coeff)
                }
                {
                    let point_1 := mload(0x0320)
                    let point_2 := mload(0x0340)
                    let coeff
                    coeff := addmod(point_1, sub(r, point_2), r)
                    coeff := mulmod(coeff, mload(0x03a0), r)
                    mstore(0x40, coeff)
                    coeff := addmod(point_2, sub(r, point_1), r)
                    coeff := mulmod(coeff, mload(0x03c0), r)
                    mstore(0x60, coeff)
                }
                {
                    let point_0 := mload(0x0300)
                    let point_2 := mload(0x0340)
                    let point_3 := mload(0x0360)
                    let coeff
                    coeff := addmod(point_0, sub(r, point_2), r)
                    coeff := mulmod(coeff, addmod(point_0, sub(r, point_3), r), r)
                    coeff := mulmod(coeff, mload(0x0380), r)
                    mstore(0x80, coeff)
                    coeff := addmod(point_2, sub(r, point_0), r)
                    coeff := mulmod(coeff, addmod(point_2, sub(r, point_3), r), r)
                    coeff := mulmod(coeff, mload(0x03c0), r)
                    mstore(0xa0, coeff)
                    coeff := addmod(point_3, sub(r, point_0), r)
                    coeff := mulmod(coeff, addmod(point_3, sub(r, point_2), r), r)
                    coeff := mulmod(coeff, mload(0x03e0), r)
                    mstore(0xc0, coeff)
                }
                {
                    let point_2 := mload(0x0340)
                    let point_3 := mload(0x0360)
                    let coeff
                    coeff := addmod(point_2, sub(r, point_3), r)
                    coeff := mulmod(coeff, mload(0x03c0), r)
                    mstore(0xe0, coeff)
                    coeff := addmod(point_3, sub(r, point_2), r)
                    coeff := mulmod(coeff, mload(0x03e0), r)
                    mstore(0x0100, coeff)
                }
                {
                    success := batch_invert(success, 0, 0x0120, r)
                    let diff_0_inv := mload(0x00)
                    mstore(0x0420, diff_0_inv)
                    for
                        {
                            let mptr := 0x0440
                            let mptr_end := 0x04a0
                        }
                        lt(mptr, mptr_end)
                        { mptr := add(mptr, 0x20) }
                    {
                        mstore(mptr, mulmod(mload(mptr), diff_0_inv, r))
                    }
                }
                {
                    let coeff := mload(0x20)
                    let zeta := mload(ZETA_MPTR)
                    let r_eval := 0
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x2364), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, mload(QUOTIENT_EVAL_MPTR), r), r)
                    for
                        {
                            let mptr := 0x2884
                            let mptr_end := 0x2364
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x20) }
                    {
                        r_eval := addmod(mulmod(r_eval, zeta, r), mulmod(coeff, calldataload(mptr), r), r)
                    }
                    for
                        {
                            let mptr := 0x2344
                            let mptr_end := 0x1bc4
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x20) }
                    {
                        r_eval := addmod(mulmod(r_eval, zeta, r), mulmod(coeff, calldataload(mptr), r), r)
                    }
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x3284), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x3224), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x31c4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x3164), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x3104), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x30a4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x3044), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x2fe4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x2f84), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x2f24), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x2ec4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x2e64), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x2e04), r), r)
                    for
                        {
                            let mptr := 0x1884
                            let mptr_end := 0x1544
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x20) }
                    {
                        r_eval := addmod(mulmod(r_eval, zeta, r), mulmod(coeff, calldataload(mptr), r), r)
                    }
                    mstore(0x04a0, r_eval)
                }
                {
                    let zeta := mload(ZETA_MPTR)
                    let r_eval := 0
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x1bc4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x1a24), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x1ba4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x1a04), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x1b84), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x19e4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x1b64), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x19c4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x1b44), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x19a4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x1b24), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x1984), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x1b04), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x1964), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x1ae4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x1944), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x1ac4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x1924), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x1aa4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x1904), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x1a84), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x18e4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x1a64), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x18c4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x1a44), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x18a4), r), r)
                    r_eval := mulmod(r_eval, mload(0x0440), r)
                    mstore(0x04c0, r_eval)
                }
                {
                    let zeta := mload(ZETA_MPTR)
                    let r_eval := 0
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x2d64), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x2d24), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x2d44), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x2d04), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x2cc4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x2ce4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x2ca4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x2c64), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x2c84), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x2c44), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x2c04), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x2c24), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x2be4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x2ba4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x2bc4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x2b84), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x2b44), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x2b64), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x2b24), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x2ae4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x2b04), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x2ac4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x2a84), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x2aa4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x2a64), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x2a24), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x2a44), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x2a04), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x29c4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x29e4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x29a4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x2964), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x2984), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x2944), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x2904), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x2924), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x28e4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x28a4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x28c4), r), r)
                    r_eval := mulmod(r_eval, mload(0x0460), r)
                    mstore(0x04e0, r_eval)
                }
                {
                    let zeta := mload(ZETA_MPTR)
                    let r_eval := 0
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x3244), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x3264), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x31e4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x3204), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x3184), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x31a4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x3124), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x3144), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x30c4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x30e4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x3064), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x3084), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x3004), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x3024), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x2fa4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x2fc4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x2f44), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x2f64), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x2ee4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x2f04), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x2e84), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x2ea4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x2e24), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x2e44), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x2dc4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x2de4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x2d84), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x2da4), r), r)
                    r_eval := mulmod(r_eval, mload(0x0480), r)
                    mstore(0x0500, r_eval)
                }
                {
                    let sum := mload(0x20)
                    mstore(0x0520, sum)
                }
                {
                    let sum := mload(0x40)
                    sum := addmod(sum, mload(0x60), r)
                    mstore(0x0540, sum)
                }
                {
                    let sum := mload(0x80)
                    sum := addmod(sum, mload(0xa0), r)
                    sum := addmod(sum, mload(0xc0), r)
                    mstore(0x0560, sum)
                }
                {
                    let sum := mload(0xe0)
                    sum := addmod(sum, mload(0x0100), r)
                    mstore(0x0580, sum)
                }
                {
                    for
                        {
                            let mptr := 0x00
                            let mptr_end := 0x80
                            let sum_mptr := 0x0520
                        }
                        lt(mptr, mptr_end)
                        {
                            mptr := add(mptr, 0x20)
                            sum_mptr := add(sum_mptr, 0x20)
                        }
                    {
                        mstore(mptr, mload(sum_mptr))
                    }
                    success := batch_invert(success, 0, 0x80, r)
                    let r_eval := mulmod(mload(0x60), mload(0x0500), r)
                    for
                        {
                            let sum_inv_mptr := 0x40
                            let sum_inv_mptr_end := 0x80
                            let r_eval_mptr := 0x04e0
                        }
                        lt(sum_inv_mptr, sum_inv_mptr_end)
                        {
                            sum_inv_mptr := sub(sum_inv_mptr, 0x20)
                            r_eval_mptr := sub(r_eval_mptr, 0x20)
                        }
                    {
                        r_eval := mulmod(r_eval, mload(NU_MPTR), r)
                        r_eval := addmod(r_eval, mulmod(mload(sum_inv_mptr), mload(r_eval_mptr), r), r)
                    }
                    mstore(R_EVAL_MPTR, r_eval)
                }
                {
                    let nu := mload(NU_MPTR)
                    mstore(0x00, calldataload(0x1424))
                    mstore(0x20, calldataload(0x1444))
                    success := ec_mul_acc(success, mload(ZETA_MPTR))
                    success := ec_add_acc(success, mload(QUOTIENT_X_MPTR), mload(QUOTIENT_Y_MPTR))
                    for
                        {
                            let mptr := 0x3900
                            let mptr_end := 0x1fc0
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x40) }
                    {
                        success := ec_mul_acc(success, mload(ZETA_MPTR))
                        success := ec_add_acc(success, mload(mptr), mload(add(mptr, 0x20)))
                    }
                    for
                        {
                            let mptr := 0x0d24
                            let mptr_end := 0x09e4
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x40) }
                    {
                        success := ec_mul_acc(success, mload(ZETA_MPTR))
                        success := ec_add_acc(success, calldataload(mptr), calldataload(add(mptr, 0x20)))
                    }
                    for
                        {
                            let mptr := 0x06a4
                            let mptr_end := 0x24
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x40) }
                    {
                        success := ec_mul_acc(success, mload(ZETA_MPTR))
                        success := ec_add_acc(success, calldataload(mptr), calldataload(add(mptr, 0x20)))
                    }
                    mstore(0x80, calldataload(0x09e4))
                    mstore(0xa0, calldataload(0x0a04))
                    for
                        {
                            let mptr := 0x09a4
                            let mptr_end := 0x06a4
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x40) }
                    {
                        success := ec_mul_tmp(success, mload(ZETA_MPTR))
                        success := ec_add_tmp(success, calldataload(mptr), calldataload(add(mptr, 0x20)))
                    }
                    success := ec_mul_tmp(success, mulmod(nu, mload(0x0440), r))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    nu := mulmod(nu, mload(NU_MPTR), r)
                    mstore(0x80, calldataload(0x1064))
                    mstore(0xa0, calldataload(0x1084))
                    for
                        {
                            let mptr := 0x1024
                            let mptr_end := 0x0d24
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x40) }
                    {
                        success := ec_mul_tmp(success, mload(ZETA_MPTR))
                        success := ec_add_tmp(success, calldataload(mptr), calldataload(add(mptr, 0x20)))
                    }
                    success := ec_mul_tmp(success, mulmod(nu, mload(0x0460), r))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    nu := mulmod(nu, mload(NU_MPTR), r)
                    mstore(0x80, calldataload(0x13e4))
                    mstore(0xa0, calldataload(0x1404))
                    for
                        {
                            let mptr := 0x13a4
                            let mptr_end := 0x1064
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x40) }
                    {
                        success := ec_mul_tmp(success, mload(ZETA_MPTR))
                        success := ec_add_tmp(success, calldataload(mptr), calldataload(add(mptr, 0x20)))
                    }
                    success := ec_mul_tmp(success, mulmod(nu, mload(0x0480), r))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    mstore(0x80, mload(G1_X_MPTR))
                    mstore(0xa0, mload(G1_Y_MPTR))
                    success := ec_mul_tmp(success, sub(r, mload(R_EVAL_MPTR)))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    mstore(0x80, calldataload(0x32a4))
                    mstore(0xa0, calldataload(0x32c4))
                    success := ec_mul_tmp(success, sub(r, mload(0x0400)))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    mstore(0x80, calldataload(0x32e4))
                    mstore(0xa0, calldataload(0x3304))
                    success := ec_mul_tmp(success, mload(MU_MPTR))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    mstore(PAIRING_LHS_X_MPTR, mload(0x00))
                    mstore(PAIRING_LHS_Y_MPTR, mload(0x20))
                    mstore(PAIRING_RHS_X_MPTR, calldataload(0x32e4))
                    mstore(PAIRING_RHS_Y_MPTR, calldataload(0x3304))
                }
            }

            // Random linear combine with accumulator
            if mload(HAS_ACCUMULATOR_MPTR) {
                mstore(0x00, mload(ACC_LHS_X_MPTR))
                mstore(0x20, mload(ACC_LHS_Y_MPTR))
                mstore(0x40, mload(ACC_RHS_X_MPTR))
                mstore(0x60, mload(ACC_RHS_Y_MPTR))
                mstore(0x80, mload(PAIRING_LHS_X_MPTR))
                mstore(0xa0, mload(PAIRING_LHS_Y_MPTR))
                mstore(0xc0, mload(PAIRING_RHS_X_MPTR))
                mstore(0xe0, mload(PAIRING_RHS_Y_MPTR))
                let challenge := mod(keccak256(0x00, 0x100), r)

                // [pairing_lhs] += challenge * [acc_lhs]
                success := ec_mul_acc(success, challenge)
                success := ec_add_acc(success, mload(PAIRING_LHS_X_MPTR), mload(PAIRING_LHS_Y_MPTR))
                mstore(PAIRING_LHS_X_MPTR, mload(0x00))
                mstore(PAIRING_LHS_Y_MPTR, mload(0x20))

                // [pairing_rhs] += challenge * [acc_rhs]
                mstore(0x00, mload(ACC_RHS_X_MPTR))
                mstore(0x20, mload(ACC_RHS_Y_MPTR))
                success := ec_mul_acc(success, challenge)
                success := ec_add_acc(success, mload(PAIRING_RHS_X_MPTR), mload(PAIRING_RHS_Y_MPTR))
                mstore(PAIRING_RHS_X_MPTR, mload(0x00))
                mstore(PAIRING_RHS_Y_MPTR, mload(0x20))
            }

            // Perform pairing
            success := ec_pairing(
                success,
                mload(PAIRING_LHS_X_MPTR),
                mload(PAIRING_LHS_Y_MPTR),
                mload(PAIRING_RHS_X_MPTR),
                mload(PAIRING_RHS_Y_MPTR)
            )

            // Revert if anything fails
            if iszero(success) {
                revert(0x00, 0x00)
            }

            // Return 1 as result if everything succeeds
            mstore(0x00, 1)
            return(0x00, 0x20)
        }
    }
}