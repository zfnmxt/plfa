This repo is for stupid shit endeavors with @OlaRonning.

Sometimes this stupid shit requires submodules (useful for PLFA):

# Cloning
```
git clone --recurse-submodules git@github.com:zfnmxt/plfa_with_ola.git
```

or if you forget the `--recurse-submodules` flag this works too
after cloning

```
git submodule init
git submodule update
```

# Add your PLFA repo
Inside of the project root.
```
git submodule add <repository_url> <path_to_directory>
```
