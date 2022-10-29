<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Modular Finite Maps over Ordered Types

[![Docker CI][docker-action-shield]][docker-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]

[docker-action-shield]: https://github.com/coq-community/coq-mmaps/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/coq-community/coq-mmaps/actions?query=workflow:"Docker%20CI"

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users



This project contains several implementations of finite maps,
including implementations based on AVL trees and red-black trees.
The finite maps are parameterized on arbitrary ordered types using
Coq functors. This is an updated version of the Coq Stdlib's FMaps
that is meant to complement the Stdlib's MSet library.

## Meta

- Author(s):
  - Pierre Letouzey (initial)
- Coq-community maintainer(s):
  - Pierre Letouzey ([**@letouzey**](https://github.com/letouzey))
  - Karl Palmskog ([**@palmskog**](https://github.com/palmskog))
- License: [GNU Lesser General Public License v2.1 only](LICENSE)
- Compatible Coq versions: 8.14 and later
- Additional dependencies: none
- Coq namespace: `MMaps`
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of Modular Finite Maps over Ordered Types
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mmaps
```

To instead build and install manually, do:

``` shell
git clone https://github.com/coq-community/coq-mmaps.git
cd coq-mmaps
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


## Documentation

As a starting point, you may consider [MMaps.Interface](Interface.v)
and [MMaps.demo](demo.v).

**Caveat** : This is work-in-progress, and might still change
in the future, including `MMaps.Interface`.

This is open source: patches, questions, comments are most welcome!
