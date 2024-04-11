

publish:
  #!/usr/bin/env fish
  for module in "" .core .operations .query
    ./mill scalasql[3.4.1]$module.publishLocal
  end
