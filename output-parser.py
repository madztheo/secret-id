import json
import tensorflow as tf
import numpy
import ezkl

with open('witness.json', 'r') as f:
    witness_data = json.load(f)

# Now you can access the data in the witness_data variable
print(witness_data['outputs'])
outputs = numpy.array(witness_data['outputs']).astype(int).tolist()
print(outputs[0][0])
print(ezkl.vecu64_to_float(outputs[0][0], 14))
# print(list(map(lambda x: ezkl.vecu64_to_float(x, 2), outputs)))