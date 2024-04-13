# BLE Scope

Source code implementation of ["Automatic Fingerprinting of Vulnerable BLE IoT Devices with Static UUIDs from Mobile Apps"](https://dl.acm.org/doi/10.1145/3319535.3354240) in CCS'19.


##  UUID Extraction

### How to run
### please put *android.jar* and *taintrules.json* under the same folder with *BLE_UUID_v1.jar*

```sh
java -jar BLE_UUID_v1.jar <apkPath>
```
The result will be saved under folder *res*, the file name is the *package name* of the target apk

## Citation

```
@inproceedings{zuo2019automatic,
  title={Automatic fingerprinting of vulnerable ble iot devices with static uuids from mobile apps},
  author={Zuo, Chaoshun and Wen, Haohuang and Lin, Zhiqiang and Zhang, Yinqian},
  booktitle={Proceedings of the 2019 ACM SIGSAC Conference on Computer and Communications Security},
  pages={1469--1483},
  year={2019}
}
```