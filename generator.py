import os
import json
import ezkl
import asyncio
from PIL import Image
import numpy
import tensorflow as tf

def transform_img(img_path):
    img_data = Image.open(os.path.join(img_path)).convert("RGB")
    x = numpy.asarray(img_data)
    img = tf.image.resize(tf.convert_to_tensor(x), [28, 28])
    img = tf.image.rgb_to_grayscale(img)
    x = img.numpy() / 255.0
    data_array = x.reshape([-1]).tolist()
    data = dict(input_data = [data_array])
    return data

async def main():
    model_path = os.path.join("mnist-classifier.onnx")
    compiled_model_path = os.path.join("compiled_model.ezkl")
    pk_path = os.path.join("key.pk")
    vk_path = os.path.join("key.vk")
    settings_path = os.path.join("settings.json")
    srs_path = os.path.join("kzg.srs")
    witness_path = os.path.join("witness.json")
    # data_path = os.path.join("sample_input.json")
    # cal_data_path = os.path.join("sample_input.json")
    data_path = os.path.join("input.json")
    cal_data_path = os.path.join("cal_data.json")
    sol_code_path = os.path.join("verifier.sol")
    abi_path = os.path.join("verifier.abi")
    address_path = os.path.join("address.json")

    # calibration data
    json.dump(transform_img("images/three.png"), open(cal_data_path, 'w' ))

    # input data
    json.dump(transform_img("images/six.png"), open(data_path, 'w' ))

    run_args = ezkl.PyRunArgs()
    run_args.input_visibility = "private"
    run_args.param_visibility = "fixed"
    run_args.output_visibility = "public"
    run_args.variables = [("batch_size", 1)]

    res = ezkl.gen_settings(model_path, settings_path)
    print(res)
    assert res == True
    print("settings generated")

    res = await ezkl.calibrate_settings(cal_data_path, model_path, settings_path, "resources/col-overflow", scales = [0, 7])
    print("calibrated")

    res = ezkl.compile_circuit(model_path, compiled_model_path, settings_path)
    assert res == True
    print("compiled")
 
    res = ezkl.get_srs(srs_path, settings_path)
    print("srs generated")

    res = ezkl.setup(compiled_model_path, vk_path, pk_path, srs_path)
    print("setup done")

    assert res == True
    assert os.path.isfile(vk_path)
    assert os.path.isfile(pk_path)
    assert os.path.isfile(settings_path)

    witness_path = os.path.join("witness.json")

    res = ezkl.gen_witness(data_path, compiled_model_path, witness_path)
    assert os.path.isfile(witness_path)
    print("witness generated")

    proof_path = os.path.join("proof.json")

    proof = ezkl.prove(witness_path, compiled_model_path, pk_path, proof_path, srs_path, "single")
    print("proof generated")

    print(proof)
    assert os.path.isfile(proof_path)

    res = ezkl.verify(proof_path, settings_path, vk_path, srs_path)
    print("verified")

    res = ezkl.create_evm_verifier(
        vk_path,
        srs_path,
        settings_path,
        sol_code_path,
        abi_path,
    )
    assert res == True
    print("smart contract verifier created")

    res = ezkl.deploy_evm(
        address_path,
        sol_code_path,
        'http://127.0.0.1:8545'
    )

    assert res == True
    print("smart contract verifier deployed")
    
    with open(address_path, 'r') as file:
        addr = file.read().rstrip()

    res = ezkl.verify_evm(
        proof_path,
        addr,
        "http://127.0.0.1:8545"
    )
    assert res == True
    print("proof verified on-chain")


asyncio.run(main())