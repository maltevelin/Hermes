src_dir = src

.PHONY: hermes_src

hermes_src:
	make -C $(src_dir)

clean:
	make -C $(src_dir) clean
