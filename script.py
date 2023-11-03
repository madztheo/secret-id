import os
import json
import ezkl
import asyncio
from PIL import Image
import numpy

def transform_img_to_array(img_path):
    img_data = Image.open(os.path.join(img_path))
    x = numpy.asarray(img_data) / 255.0
    data_array = x.reshape([-1]).tolist(),
    data = dict(input_data = data_array),
    return data

async def main():
    model_path = os.path.join("model.onnx")
    compiled_model_path = os.path.join("compiled_model.ezkl")
    pk_path = os.path.join("key.pk")
    vk_path = os.path.join("key.vk")
    settings_path = os.path.join("settings.json")
    srs_path = os.path.join("kzg.srs")
    witness_path = os.path.join("witness.json")
    data_path = os.path.join("input.json")
    cal_data_path = os.path.join("cal_data.json")

    # calibration data
    json.dump(transform_img_to_array("images/virginia.jpg"), open(cal_data_path, 'w' ))

    # input data
    json.dump(transform_img_to_array("images/washington.jpg"), open(data_path, 'w' ))

    res = ezkl.gen_settings(model_path, settings_path)
    print(res)
    assert res == True
    print("settings generated")

    res = await ezkl.calibrate_settings(cal_data_path, model_path, settings_path, "resources")
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

    proof = ezkl.gen_proof(witness_path, compiled_model_path, pk_path, proof_path, srs_path, "single")
    print("proof generated")

    print(proof)
    assert os.path.isfile(proof_path)

    res = ezkl.verify_proof(proof_path, settings_path, vk_path, srs_path)
    print("verified")


asyncio.run(main())