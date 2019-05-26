TESTS=mutation.test plugin.test

.PHONY: test $(TESTS)

test: $(TESTS)

MUTATION=mutation

mutation.test:
	cd $(MUTATION)/; sh $(MUTATION).sh

plugin.test:
	cd plugin/; sh plugin.sh
