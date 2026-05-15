# Build the docker
docker build -t cmdo_img:latest .

# Show all imgs
docker images
echo -e "-------------------------------------------------------------------------\n"

# Execute docker imgdocker  (it->interactive terminal  -v->create a mount point)
docker run --rm -it -v $(pwd)/res/SAT/outputs:/app/outputs/SAT -v $(pwd)/res/CP/outputs:/app/outputs/CP -v $(pwd)/res/MIP/outputs:/app/outputs/MIP cmdo_img


# Uncomment if you want to navigate docker filesystem
# docker run -it cmdo_img bash  
