for file in * ; do
    mv -v "$file" "${file#*-}"
done