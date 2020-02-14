LIQUID=stack exec -- liquid
STACK=stack --flag lazuli:liquidhaskell
MODELS=$(patsubst train_%.py,models/%.hs,$(wildcard train_*.py))
BENCHMARK_START=1
BENCHMARK_STOP=100
BENCHMARK_STEP=1
BENCHMARK_IDS=$(shell seq $(BENCHMARK_START) $(BENCHMARK_STEP) $(BENCHMARK_STOP))
BENCHMARKS_HS=$(foreach n_params,$(BENCHMARK_IDS),bench/Random_$(n_params)_Linear_1.hs)
BENCHMARKS_H5=$(foreach n_params,$(BENCHMARK_IDS),bench/Random_$(n_params)_Linear_1.h5)
BENCHMARKS_H5_HD=$(word 1,$(BENCHMARKS_H5))
BENCHMARKS_H5_TL=$(wordlist 2,$(words $(BENCHMARKS_H5)),$(BENCHMARKS_H5))


.PHONY: build
build:
	$(STACK) build


.PHONY: test
test:
	$(LIQUID) -isrc models/AND_Gate_2_Sigmoid_1.hs
	$(STACK) test


.PHONY: clean
clean:
	stack clean


.PHONY: train
train: $(MODELS)

models/:
	mkdir -p models

models/%.h5: train_%.py | models/
	python $<

models/%.hs: models/%.h5
	python convert.py -i $< -o $@


.PHONY: benchmark
benchmark: $(BENCHMARKS_HS)

bench/:
	mkdir -p bench

$(BENCHMARKS_H5_HD): mk_bench.py | bench/
	python mk_bench.py

define BENCHMARK_H5_template
$(1): $(BENCHMARKS_H5_HD)
	@if test -f $$@; then :; else \
		rm -f $(BENCHMARKS_H5_HD); \
		$(MAKE) $(AM_MAKEFLAGS) $(BENCHMARKS_H5_HD); \
	fi
endef

$(foreach bm,$(BENCHMARKS_H5_TL),$(eval $(call BENCHMARK_H5_template,$(bm))))

bench/%.hs: bench/%.h5
	python convert.py -i $< -o $@
