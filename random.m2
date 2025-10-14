---Installing package from scratch

uninstallPackage "WittVectors"
restart
path = append(path, "~/GitHub/WittVectors")
installPackage ("WittVectors", InstallPrefix => "~/GitHub/WittVectors")
