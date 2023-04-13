all :
	-(cd src/ && make all)

clean:
	-(cd src/ && make distclean)
	-rm jlc
