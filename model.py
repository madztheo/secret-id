import numpy as np
from doctr.models import ocr_predictor, db_resnet50, crnn_vgg16_bn
from doctr.utils.visualization import visualize_page
from doctr.models.utils import export_model_to_onnx
from PIL import Image
import numpy
import os
import torch
import matplotlib.pyplot as plt
import tensorflow as tf
from doctr.io import DocumentFile

def transform_img_to_array(img_path):
    img_data = Image.open(os.path.join(img_path))
    x = numpy.asarray(img_data)
    return x

#model = ocr_predictor('db_resnet50', 'crnn_vgg16_bn', pretrained=True)
detection_model = db_resnet50(pretrained=True, exportable=True)
recognition_model = crnn_vgg16_bn(pretrained=True, exportable=True)
input_page = DocumentFile.from_images("images/washington.jpg")
input_tensor = tf.random.uniform([1, 1024, 1024, 3], maxval=255, dtype=tf.int32)
# input_tensor = tf.convert_to_tensor(input_page)
# dummy_input = torch.randint(0, 255, (460, 680, 3), dtype=torch.uint8).numpy()
# detection_model_output = detection_model(input_tensor)
# print(detection_model_output)
# print(recognition_model)
# out = recognition_model(dict(conv2d_10_input = detection_model_output["logits"]))
# out = model(input_page)
# print(out)
# visualize_page(out.pages[0].export(), input_page[0])
# plt.show()
# model_path = export_model_to_onnx(detection_model, model_name='model.onnx', dummy_input=torch.randn(1, 1024, 1024, 3).tolist())
# model_path = export_model_to_onnx(recognition_model, model_name='model.onnx', dummy_input=[dummy_input])