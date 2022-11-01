Armv8 Memory Model
==================

Port of Viktor Vafeiadis's [Coq formalization of the Armv8 Memory Model](https://github.com/vafeiadis/arm-model), which is based on the official [mixed-size Armv8 memory model](https://github.com/herd/herdtools7/blob/95785c747750be4a3b64adfab9d5f5ee0ead8240/herd/libdir/aarch64.cat) and associated [paper](https://doi.org/10.1145/3458926).

Three formulations of the Armv8 memory model are defined:

- [arm8_evScript.sml](./arm8_evScript.sml) - [External visibility requirement](https://github.com/herd/herdtools7/blob/bc812296f48764963b6cb9bb51c2d88f3cc99b4b/herd/libdir/arm-models/mixed/ev.cat)
- [arm8_ecScript.sml](./arm8_ecScript.sml) - [External completion requirement](https://github.com/herd/herdtools7/blob/bc812296f48764963b6cb9bb51c2d88f3cc99b4b/herd/libdir/arm-models/mixed/ec.cat)
- [arm8_egcScript.sml](./arm8_egcScript.sml) - [External global completion requirement](https://github.com/herd/herdtools7/blob/bc812296f48764963b6cb9bb51c2d88f3cc99b4b/herd/libdir/arm-models/mixed/egc.cat)

These models and proved to be equivalent in [arm8_equivScript.sml](./arm8_equivScript.sml).