KOKAC = kokac

.PHONY: all clean

all: build

build:
	dune build src/$(KOKAC).exe

install:
	ln -sf _build/default/src/$(KOKAC).exe $(KOKAC)

clean:
	dune clean
	rm -f $(KOKAC)
