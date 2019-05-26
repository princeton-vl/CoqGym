# Contribute to QuickChick

The master branch of QuickChick is pull-request based only.
It is used to track the developmental branch of Coq for use in the Coq CI. 

Changes that specifically aim at forward compatibility with unreleased versions
of Coq should be proposed to master branch.

Otherwise, if you are proposing a fix or improvement, please submit the PR to
corresponding branch:

- `master` works with `coq.dev`
- `8.*`    works with the specific version of Coq

Please state the compatibility with other Coq versions in your pull request.

Our next release will be based on `8.9` branch by default, unless older branches
require a critical fix.
