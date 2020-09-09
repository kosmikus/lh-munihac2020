# Liquid Haskell

This repository accompanies the MuniHac 2020 Workshop on Liquid Haskell.

We are going to use the new Liquid Haskell GHC plugin.

If you want to follow along with the workshop, please clone this repository
and try to build it:

- **You need the [`z3`](https://github.com/Z3Prover/z3) theorem prover
  installed and in your PATH. (This is a non-Haskell dependency, so you
  have to install it separately.)**

- If you can, use GHC 8.10.2. GHC 8.10.1 should also work, but if you want
  to use `ghcide` with Liquid Haskell properly, you will need 8.10.2.

- I will use `cabal`, but the package should also be buildable with `stack`.

- If the package builds successfully, then as part of the build output for
  the `Tutorial` module in this package you should see the text
  `LIQUID: SAFE (3 constraints checked)`. If you can see this, the plugin
  seems to be working correctly.

- Unfortunately, Windows support for plugins is known to be unreliable.
  If you are on Windows, the above may just not work. You may still have the
  option to install the `liquidhaskell` package on your system, giving you
  an executable called `liquid`, and running `liquid` on `Tutorial.hs` via
  the command line.
