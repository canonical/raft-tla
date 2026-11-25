for file in *.tla; do
    tlapm --strict --threads 4 --stretch 4 --nofp $file
done
