ClientCentric2PLBug.tla: ClientCentric2PL.tla
	sed 's/with tId \\in voted \\/with tId \\in transactions \\/g' $< > $@
	sed -i '' 's/ClientCentric2PL/ClientCentric2PLBug/g' $@
	# Requires `pip3 install tlacli`
	tlacli translate $@  