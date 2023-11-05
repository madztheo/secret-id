import json
import tensorflow as tf
import numpy
import ezkl

with open('witness.json', 'r') as f:
    witness_data = json.load(f)

def convert_to_float(array):
    for i in range(len(array)):
        for j in range(len(array[i])):
            array[i][j] = ezkl.vecu64_to_float(array[i][j], 14)
    return array

# Now you can access the data in the witness_data variable
outputs = numpy.array(witness_data['outputs'], dtype=numpy.uint).tolist()
float_array = convert_to_float(outputs)
normalized_array = tf.nn.softmax(tf.convert_to_tensor(float_array)).numpy().astype(numpy.float32).tolist()

# Get the number with the highest confidence
prediction = numpy.argmax(normalized_array[0])
print(prediction)